import type { EngineInterface, Register, RenderElement, RenderInput } from 'claude-code'

// `/q <text>` while a turn is running holds the text in a stack drawn above
// the prompt box, sent once the turn has ended, in order, one turn each. The
// band's buttons and /q reorder, edit, remove, flush. `[ ▶ ]` is the way into
// the running turn: the entry rides its next tool result as context, which is
// how the engine delivers a mid-turn message. Enter alone is left as stock.

const COMMAND = 'q'
/** `[ ↑ ] [ ↓ ] [ ▶ ] [ edit ] [ ✕ ]`, each with the gap before it, and the one before the text */
const CONTROLS = 34
/** what a steered row says while it waits, and `[ ✕ ]` after it, gaps and all */
const MARK = 'waiting for the next tool call'
const STEER_CONTROLS = MARK.length + 8
/** the two columns the band's frame takes off `bodyColumns` */
const BORDER = 2
/** the band's one colour, spent on the steer route alone: `▶` and a stack in flight */
const ACCENT = 'cyan'
const NO_MOUSE = 'clicks need /tui fullscreen · here: ctrl+x tab, Tab to a button, Enter'
/** the engine refuses a plugin's prompt within 5s of its last: wait that out */
const GAP_MS = 5200
/** the engine caps a tool result's context: a push past it waits for the turn's end instead */
const CONTEXT_MAX = 32000
/** refusals in a row before the drain stops and waits for /q send */
const RETRIES = 3
/** how long a live /tasks answer is trusted */
const BUSY_CACHE_MS = 2000
/** the wait between probes while the engine reports work running (long: each
    probe runs /tasks like the user typed it, and a slow poll still catches
    the drain at turn boundaries and task-notifications anyway) */
const PROBE_RETRY_MS = 10_000
/** unclassifiable probes in a row before the drain trusts a clear Stop answer
    instead — it punishes a broken classifier, never genuinely running work */
const UNKNOWN_GIVE_UP = 3
/** how recent a Stop that named its background tasks must be to answer for the engine */
const TRUST_STOP_MS = 60_000
/** tries, and the wait between them, for the ring to reach a field just drawn */
const FOCUS_TRIES = 6
const FOCUS_MS = 60

type Entry = { id: string; text: string; at: number }

let stack: Entry[] = []
/** taken out of the stack by `[ ▶ ]` to ride the running turn's next tool result */
let steer: Entry[] = []
/** the plugin's `joined` option: the whole stack as one prompt */
let joined = false
/** the running main-loop turn, so the band and /q send know idle from busy */
let turnId: string | undefined
/** one drain per turn, whatever else raises turn.complete for it */
let drainedTurn: string | undefined
let counter = 0
/** when the last prompt of ours went out, and the timer waiting out the gap */
let sentAt = 0
let pending: { cancel: () => void } | null = null
let failures = 0
/** the row being typed in: the entry's id and the field's text so far */
let editing: { id: string; text: string } | null = null
/** the ring reached the field: only then does it leaving mean Esc */
let editFocused = false
/** the band's instance, for `$.ui.focus`; the band draws under one id */
let bandRequest: string | undefined
/** read off /q: the classic renderer sends the band no mouse, so the band says how else */
let fullscreen: boolean | undefined
/** the engine's count of background work (subagents, shells, monitors) still running at the last Stop */
let inFlight = 0
/** the last Stop came without background_tasks at all: its silence is not an empty list */
let stopBlind = false
/** when the last Stop answered with a real background_tasks array */
let stopAt = 0
/** a live /tasks answer, kept for a beat so a burst of drain decisions asks once */
let busyCache: { at: number; running: boolean } | null = null
/** unclassifiable probes in a row, for the give-up backstop */
let unknowns = 0
/** whether the answer behind the current busy verdict was unclassifiable */
let lastUnknown = false
/** a gate verdict is in flight between its arming and its answer */
let gating = false

const firstLine = (text: string) => text.trim().split('\n')[0]?.trim() ?? ''

/** the raw first line, which the field edits, and the rest it leaves alone */
const head = (text: string) => text.split('\n')[0] ?? ''
const withHead = (text: string, line: string) => [line, ...text.split('\n').slice(1)].join('\n')

const fit = (text: string, room: number) => {
  const chars = [...text]
  return chars.length <= room ? text : `${chars.slice(0, Math.max(1, room - 1)).join('')}…`
}

/** what the header says, and whether that is a stack on the move: the accent's cue */
const state = (): [word: string, moving: boolean] =>
  steer.length > 0 && turnId
    ? ['going into the turn', true]
    : stack.length === 0
      ? ['nothing held', false]
      : turnId
        ? ['sent when the turn ends', false]
        : inFlight > 0 && !pending
          ? [`sent when the background work ends · ${inFlight} running`, false]
          : pending
            ? ['going out', true]
            : ['sending', true]

/** one line for a "it did not send" report: every flag the drain reads */
const statusLine = () =>
  `turn ${turnId ? 'running' : 'idle'}${inFlight > 0 ? ` · ${inFlight} in the background` : stopBlind ? ' · background unknown' : ''} · ${stack.length} held${steer.length > 0 ? ` · ${steer.length} going into the turn` : ''} · ${pending && !turnId ? 'going out' : 'waiting'}`

const indexOfId = (id: string) => stack.findIndex(entry => entry.id === id)

const removeAt = (index: number): Entry | undefined => {
  const [gone] = stack.splice(index, 1)
  return gone
}

// a press acts on the drawing it was drawn in, which the stack may have moved under
const removeId = (id: string): Entry | undefined => {
  const index = indexOfId(id)
  return index < 0 ? undefined : removeAt(index)
}

/** entry `from` lands at `to`, the rest closing up behind it */
const moveAt = (from: number, to: number) => {
  if (from < 0 || to < 0 || to >= stack.length || from === to) return false
  const [entry] = stack.splice(from, 1)
  stack.splice(to, 0, entry!)
  return true
}

// the engine refuses a prompt that starts with a slash: the person meant a
// command, and it is run as one when its turn comes
const slash = (text: string): { command: string; args: string } | undefined => {
  const match = /^\/(\S+)\s*([^]*)$/.exec(text)
  return match ? { command: match[1]!, args: match[2]! } : undefined
}

/** the next prompt out: the first entry, or under `joined` the stack up to its first command */
const takeDue = (): Entry[] => {
  if (!joined || slash(stack[0]!.text)) return stack.splice(0, 1)
  const upTo = stack.findIndex(entry => slash(entry.text))
  return stack.splice(0, upTo < 0 ? stack.length : upTo)
}

// Synchronous up to the submit itself, so two sends landing together (a
// turn's end and a press) cannot both take an entry: the second one sees
// sentAt and waits the gap out. The submit is not awaited: it resolves only
// once the prompt entered, which is after the hook that asked for it answered.
const flush = ($: EngineInterface) => {
  pending = null
  if (stack.length === 0) return
  // a turn started under the timer: nothing is sent into one, and its own end
  // arms the next drain
  if (turnId) return
  const wait = GAP_MS - (Date.now() - sentAt)
  if (wait > 0) {
    pending = $.clock.after(wait, () => flush($))
    $.ui.invalidate('ui.render')
    return
  }
  const going = takeDue()
  sentAt = Date.now()
  if (editing && indexOfId(editing.id) < 0) editing = null
  $.ui.invalidate('ui.render')
  const run = slash(going[0]!.text)
  if (run) {
    $.command
      .run(run)
      // an unknown name, or one refused: nothing a retry would change
      .catch(err => $.ui.log(`queue: /${run.command} did not run: ${err}`))
      // a turn the command started drains at its end; none started leaves the rest to go now
      .then(() => {
        failures = 0
        if (stack.length > 0 && !turnId) send($)
      })
    return
  }
  $.prompt
    .submit({ text: going.map(entry => entry.text).join('\n\n') })
    .then(() => void (failures = 0))
    .catch(err => {
      // back as they were, ids and all, so the band's buttons still find them
      stack.unshift(...going)
      $.ui.log(`queue: the held prompt did not go out: ${err}`)
      // a refusal is usually the gap: try once it has passed; several in a row
      // (the session's cap on a plugin's prompts) leave the stack to /q send
      if (++failures < RETRIES) pending = $.clock.after(GAP_MS, () => flush($))
      $.ui.invalidate('ui.render')
    })
}

// Off the raising hook's dispatch: a submit from inside command.run, ui.press
// or ui.render is refused, as it would wait on the turn that hook holds.
const send = ($: EngineInterface) => {
  failures = 0
  armGate($)
}

// Only one gate runs at a time, whatever raises it.
const armGate = ($: EngineInterface) => {
  if (pending || gating) return
  pending = $.clock.after(0, () => gate($))
}

// The Stop snapshot is the only background count the mod holds, and it can
// lie: a Ctrl+B move can race past it, and a surface that omits
// background_tasks reads as an engine with nothing running. Before anything
// leaves the stack on a count of zero, ask the engine live.
const gate = async ($: EngineInterface) => {
  pending = null
  if (stack.length === 0 || turnId) return
  gating = true
  let running: boolean
  try {
    running = inFlight > 0 || (await backgroundRunning($))
  } catch {
    running = false
  } finally {
    gating = false
  }
  if (!running) return void flush($)
  // only a classifier that never makes sense gets overruled; genuinely running
  // work is waited out however long it takes (a turn boundary or a clear
  // probe ends the wait)
  if (lastUnknown && ++unknowns >= UNKNOWN_GIVE_UP) {
    unknowns = 0
    $.ui.log('queue: the tasks answer never made sense · sending anyway')
    return void flush($)
  }
  if (!lastUnknown) unknowns = 0
  pending = $.clock.after(PROBE_RETRY_MS, () => gate($))
  $.ui.invalidate('ui.render')
}

const backgroundRunning = async ($: EngineInterface): Promise<boolean> => {
  lastUnknown = false
  if (busyCache && Date.now() - busyCache.at < BUSY_CACHE_MS) return busyCache.running
  let running: boolean
  try {
    const r = (await $.command.run({ command: 'tasks', args: '' })) as { text?: string } | undefined
    const text = r?.text ?? ''
    const verdict = classifyTasks(text)
    if (verdict !== undefined) running = verdict
    else if (!stopBlind && Date.now() - stopAt < TRUST_STOP_MS) running = false
    else {
      // no usable answer and no recent trustworthy Stop: hold the queue and
      // tell on itself, so a format change becomes a logged, reportable pause
      // instead of either a premature send or a silent wedge
      lastUnknown = true
      running = true
      $.ui.log(`queue: cannot read the tasks answer · treating as busy: ${JSON.stringify(text.slice(0, 200))}`)
    }
  } catch {
    // no /tasks to ask (headless, refused, renamed): the old behavior
    running = false
  }
  busyCache = { at: Date.now(), running }
  return running
}

const classifyTasks = (text: string): boolean | undefined => {
  const body = text.trim()
  if (body === '' || /^\W*no\b.{0,20}\btasks?\b/i.test(body)) return false
  if (/\brunning\b|in the background|waiting|monitor/i.test(body)) return true
  return undefined
}

/** how old a held entry may be for its bare text to read as a queued echo */
const ECHO_WINDOW_MS = 5 * 60_000

// Some surfaces (seen on the desktop Code tab) queue the typed `/q <text>`
// line into the engine's own mid-turn message queue as well as running the
// command: the model then reads the raw line, and the stack's copy goes out
// again at idle. Drop those echoes silently: the queue and the band already
// say what is held, and the held copy arriving at idle is the whole story.
const isEcho = (raw: string): boolean => {
  const line = raw.trim()
  if (line === '') return false
  const stripped = line.replace(/^\/q\b/, '').trim()
  if (stripped !== line) {
    // the whole typed command, slash included: match it against the stack at
    // any age, and never against the plugin's own submit (its entry is
    // already out of the stack when $.prompt.submit runs)
    return stripped !== '' && stack.some(entry => entry.text.trim() === stripped)
  }
  // the bare text, queued without its command prefix: only a fresh held
  // entry counts, so the plugin's own submit (taken out before sending)
  // and an ordinary prompt pass through
  return stack.some(entry => entry.at > Date.now() - ECHO_WINDOW_MS && entry.text.trim() === line)
}

// out of the stack only once the box has it: a fill the box turned down (a
// dialog holds the keys) would otherwise lose the text
const fillFrom = ($: EngineInterface, entry: Entry) =>
  $.prompt
    .fill({ text: entry.text })
    .then(({ isFilled }) => {
      if (!isFilled) return false
      // the fill's round trip is long enough for a drain to have taken it
      const kept = removeId(entry.id) !== undefined
      $.ui.invalidate('ui.render')
      return kept
    })
    .catch(() => false)

// The row becomes a field, and the band's ring moves onto it — which the
// engine allows only while the band holds the keyboard (a click on it, ctrl+x
// tab). Where it does not, the composer takes the text as it always did.
const startEdit = ($: EngineInterface, entry: Entry) => {
  editing = { id: entry.id, text: head(entry.text) }
  editFocused = false
  $.ui.invalidate('ui.render')
  takeField($, entry, FOCUS_TRIES)
}

// The ring only lands on an element the band has already drawn, so the first
// try, a tick after the invalidate, is usually too early for the frame.
const takeField = ($: EngineInterface, entry: Entry, tries: number) => {
  const open = editing
  if (!open || !bandRequest) return
  void $.ui.focus({ requestId: bandRequest, key: `input:${open.id}` }).then(({ deny }) => {
    if (editing !== open) return
    // the engine skips the ui.focus a plugin raised itself (re-entry), so the
    // ring reaching the field is this answer and not the event
    if (!deny) return void (editFocused = true)
    if (tries > 0) return void $.clock.after(FOCUS_MS, () => takeField($, entry, tries - 1))
    // the ordinary case (a click does not give the band the keyboard): the
    // fill says what happened by itself, so nothing is written to the transcript
    editing = null
    $.ui.invalidate('ui.render')
    void fillFrom($, entry)
  })
}

const commitEdit = ($: EngineInterface, value: string) => {
  const open = editing
  editing = null
  $.ui.invalidate('ui.render')
  if (!open) return
  const entry = stack[indexOfId(open.id)]
  // an emptied field is a cancel: the entry keeps the text it had
  if (entry && value.trim() !== '') entry.text = withHead(entry.text, value)
}

/** what the model reads beside the tool result, the message framed as the user's */
const frame = (entry: Entry) =>
  `The user sent this message while you were working (delivered by the prompt-queue plugin as a steering message, the way a mid-turn message normally arrives). Address it as you continue:\n\n${entry.text}`

const removeSteer = (id: string) => {
  const index = steer.findIndex(entry => entry.id === id)
  if (index >= 0) steer.splice(index, 1)
}

/** mid-turn it rides the turn's next tool result; idle it goes to the front and out */
const sendNow = ($: EngineInterface, id: string): 'pushed' | 'sending' | undefined => {
  const index = indexOfId(id)
  if (index < 0) return
  if (!turnId) {
    moveAt(index, 0)
    send($)
    return 'sending'
  }
  if (editing?.id === id) editing = null
  const entry = removeAt(index)!
  steer.push(entry)
  // the push has no row of its own until a tool call carries it: say so now
  $.ui.log(`❯ ${entry.text} · into the turn at its next tool call`)
  return 'pushed'
}

const bandOf = ($: EngineInterface, e: RenderInput<'AbovePrompt'> & { surface: 'terminal' }): RenderElement => {
  const { Box, Text, Button, Input } = $.ui.resolve(e)
  bandRequest = e.requestId
  const gutter = String(stack.length).length + 1
  const room = Math.max(8, e.props.bodyColumns - BORDER - gutter - CONTROLS)
  const steerRoom = Math.max(8, e.props.bodyColumns - BORDER - gutter - STEER_CONTROLS)
  const press = (run: () => void) => () => {
    run()
    $.ui.invalidate('ui.render')
  }
  // the open row's own number is the only mark a field being typed in gets
  const number = (index: number, open = false) => {
    const n = String(index + 1).padStart(gutter - 1)
    return Text(open ? { bold: true, children: n } : { dimColor: true, children: n })
  }
  // dim at rest so the rows read as text; the pointer over a row brings that
  // row's controls up to full strength, the keyed row Box being the scope
  const quiet = { dimColor: true, hover: { dimColor: false } } as const
  // the two that move things along keep full strength, and take the accent on hover
  const go = { hover: { color: ACCENT } } as const
  // an end of the stack keeps the column, so the buttons beside it stay in line
  const move = (entry: Entry, index: number, delta: number, key: string, label: string) =>
    index + delta < 0 || index + delta >= stack.length
      ? Box({ width: 5 })
      : Button({
          key: `${key}:${entry.id}`,
          label,
          ...quiet,
          // by id and by step: the stack may have moved under the drawing
          onPress: press(() => void moveAt(indexOfId(entry.id), indexOfId(entry.id) + delta)),
        })
  const [word, moving] = state()
  return Box({
    flexDirection: 'column',
    borderStyle: 'round',
    borderDimColor: true,
    children: [
      // the count is what the eye goes to; the rest of the line is chrome
      Box({
        flexDirection: 'row',
        gap: 1,
        children: [
          Text({ dimColor: true, children: 'queued' }),
          Text({ dimColor: true, children: '·' }),
          Text({ bold: true, children: String(stack.length + steer.length) }),
          Text({ dimColor: true, children: '·' }),
          Text(moving ? { color: ACCENT, children: word } : { dimColor: true, children: word }),
        ],
      }),
      // first out either way: into the next tool result, or ahead of the stack
      ...steer.map(entry =>
        Box({
          key: `steer:${entry.id}`,
          flexDirection: 'row',
          gap: 1,
          children: [
            Text({ color: ACCENT, children: '▶'.padStart(gutter - 1) }),
            Box({ width: steerRoom, children: Text({ wrap: 'truncate', children: fit(firstLine(entry.text), steerRoom) }) }),
            Text({ dimColor: true, children: MARK }),
            Button({ key: `unsteer:${entry.id}`, label: '✕', ...quiet, onPress: press(() => removeSteer(entry.id)) }),
          ],
        }),
      ),
      ...stack.map((entry, index) =>
        editing?.id === entry.id
          ? Box({
              key: `row:${entry.id}`,
              flexDirection: 'row',
              gap: 1,
              children: [
                number(index, true),
                Input({
                  key: `input:${entry.id}`,
                  value: editing.text,
                  autoFocus: true,
                  submitLabel: 'keep',
                  onInput: value => void (editing && (editing.text = value)),
                  onSubmit: value => commitEdit($, value),
                }),
                // Esc gives the keys back to the composer without a word to the
                // plugin: this is the way out that leaves the entry as it was
                Button({ key: `stop:${entry.id}`, label: '✕', ...quiet, onPress: press(() => void (editing = null)) }),
              ],
            })
          : Box({
              key: `row:${entry.id}`,
              flexDirection: 'row',
              gap: 1,
              children: [
                number(index),
                Box({ width: room, children: Text({ wrap: 'truncate', children: fit(firstLine(entry.text), room) }) }),
                move(entry, index, -1, 'up', '↑'),
                move(entry, index, 1, 'down', '↓'),
                Button({ key: `now:${entry.id}`, label: '▶', ...go, onPress: press(() => sendNow($, entry.id)) }),
                Button({ key: `edit:${entry.id}`, label: 'edit', ...quiet, onPress: () => startEdit($, entry) }),
                Button({ key: `rm:${entry.id}`, label: '✕', ...quiet, onPress: press(() => void removeId(entry.id)) }),
              ],
            }),
      ),
      // the stack's own controls start where a row's do, so the whole right
      // side of the band is one column of buttons
      Box({
        key: 'all',
        flexDirection: 'row',
        paddingLeft: gutter + room + 1,
        gap: 1,
        children: [
          ...(turnId ? [] : [Button({ key: 'send', label: 'send', ...go, onPress: press(() => send($)) })]),
          Button({ key: 'clear', label: 'clear', ...quiet, onPress: press(() => void ((stack = []), (steer = []), (editing = null))) }),
        ],
      }),
      // a click that lands nowhere reads as a button that did nothing
      ...(fullscreen === false ? [Box({ paddingLeft: gutter, children: Text({ dimColor: true, children: NO_MOUSE }) })] : []),
    ],
  })
}

const listed = () => {
  const lines = [
    ...steer.map(entry => `▶ ${fit(firstLine(entry.text), 72)} · ${MARK}`),
    ...stack.map((entry, i) => `${i + 1}. ${fit(firstLine(entry.text), 72)}`),
  ]
  return [...(lines.length === 0 ? ['queue: nothing held'] : lines), statusLine()].join('\n')
}

const indexArg = (word: string): number | null => {
  const n = Number(word)
  return Number.isInteger(n) && n >= 1 && n <= stack.length ? n - 1 : null
}

export const register: Register = (on, options) => {
  joined = options.joined === true

  on('session.start', async ($, e, next) => {
    const r = await next(e)
    // nothing has run yet in this session: start trusted-idle so an early /q
    // does not hang on a /tasks answer the classifier has never seen
    stopAt = Date.now()
    stopBlind = false
    await $.command
      .register({
        name: COMMAND,
        description: 'Hold a prompt until the turn ends: /q <text>; list, up/down/mv, now, rm, edit, clear, send, status (prompt-queue)',
        argumentHint: '[<text> | up <n> | down <n> | mv <n> <m> | now <n> | rm <n> | edit <n> | clear | send | status]',
        // the queue is worked on while a turn runs, which is the only time it fills
        immediate: true,
      })
      .catch(err => $.ui.log(`queue: /${COMMAND} not registered: ${err}`))
    return r
  })

  on('turn.start', async ($, e, next) => {
    turnId = e.turnId
    busyCache = null
    // the band reads the running turn: without this it keeps saying `sending`,
    // [ send ] and all, over the turn the queue itself started
    if (stack.length > 0) $.ui.invalidate('ui.render')
    return next(e)
  })

  on('turn.complete', async ($, e, next) => {
    const r = await next(e)
    // a subagent's turn ends inside the session's own: not a moment to send
    if (e.agentId) return r
    turnId = undefined
    busyCache = null
    if (drainedTurn === e.turnId) return r
    drainedTurn = e.turnId
    // the turn called no tool after all: what was pushed into it leads the drain
    if (steer.length > 0) stack.unshift(...steer.splice(0))
    // a turn that left work running in the background is a pause, not an end:
    // the notification that wakes it starts the turn whose end drains
    if (inFlight > 0) {
      $.ui.invalidate('ui.render')
      return r
    }
    // every ending drains, an Esc included: what was typed was asked for
    send($)
    return r
  })

  // The engine's own list of what is still running in the background, on the
  // classic Stop hook's input: the one place that says whether a turn's end
  // is the work's end. Stop runs before turn.complete.
  on('classic.Stop', async ($, e, next) => {
    const tasks = (e as { background_tasks?: unknown }).background_tasks
    if (Array.isArray(tasks)) {
      inFlight = tasks.length
      stopBlind = false
      stopAt = Date.now()
    } else {
      // silence is not an answer: keep the last count and let the gate probe
      stopBlind = true
    }
    busyCache = null
    return next(e)
  })

  // A background task just reported: the cached answer is stale, and the
  // wake-turn's own end is what drains the stack. An early-access build
  // without this event must not take the whole mod down with it.
  try {
    on('session.receive', async ($, e, next) => {
      if ((e as { origin?: { kind?: string } }).origin?.kind === 'task-notification') busyCache = null
      return next(e)
    })
  } catch {
    // no task-notification signal on this build: caches still clear at turns
  }

  // The steer route: a mid-turn message rides the next tool result's context,
  // which is how the engine delivers one. The object `next` gave us goes back
  // whole, `ref` and all, so the tool's own messages are used verbatim.
  on('tool.call', async ($, e, next) => {
    const r = await next(e)
    // a subagent's call runs inside the turn but is not it
    if (steer.length === 0 || e.agentId || r.deny !== undefined) return r
    const context = [...(r.context ?? [])]
    let used = context.reduce((n, text) => n + text.length, 0)
    const going = steer.splice(0)
    for (const entry of going) {
      const framed = frame(entry)
      if (used + framed.length > CONTEXT_MAX) {
        steer.push(entry)
        continue
      }
      used += framed.length
      context.push(framed)
      $.ui.log(`pushed into the turn · ${fit(firstLine(entry.text), 72)}`)
    }
    if (steer.length > 0) $.ui.log(`queue: ${steer.length} too long for a tool result · goes when the turn ends`)
    $.ui.invalidate('ui.render')
    return context.length === (r.context?.length ?? 0) ? r : { ...r, context }
  })

  // Enter is left to the engine. Only the turn id is read off it: a reload
  // mid-turn missed turn.start, and this Enter carries the id it lost. The
  // one exception is a queued echo of a held `/q` line, dropped so the stack
  // drains once, at idle, instead of the raw text arriving early as well.
  on('prompt.submit', async ($, e, next) => {
    if (isEcho((e as { text?: string }).text ?? '')) return { drop: 'prompt-queue' }
    if (e.turnId) turnId = e.turnId
    return next(e)
  })

  // Esc, or the ring moving on, leaves the row as it was: the field is only
  // the person's while they are in it. Not before it has had the ring — a
  // click on [ edit ] lands the ring on the button first.
  on('ui.focus', { component: 'AbovePrompt' }, async ($, e, next) => {
    const r = await next(e)
    if (!editing) return r
    if (e.element === `input:${editing.id}`) editFocused = true
    else if (editFocused) {
      editing = null
      $.ui.invalidate('ui.render')
    }
    return r
  })

  on('command.run', { command: COMMAND }, async ($, e) => {
    fullscreen = e.presentation.isFullscreen
    const [word = '', value = '', target = ''] = e.args.trim().split(/\s+/)
    if (word === '') return { text: listed() }
    if (word === 'status') return { text: statusLine() }
    if (word === 'clear') {
      const n = stack.length + steer.length
      stack = []
      steer = []
      editing = null
      $.ui.invalidate('ui.render')
      return { text: `queue: ${n} cleared` }
    }
    if (word === 'up' || word === 'down' || word === 'mv' || word === 'now' || word === 'rm' || word === 'edit') {
      if (stack.length === 0) return { text: 'queue: nothing held' }
      const index = indexArg(value)
      if (index === null) return { text: `queue: /q ${word} <n>${word === 'mv' ? ' <m>' : ''}, 1 to ${stack.length}` }
      if (word === 'rm') {
        removeAt(index)
        $.ui.invalidate('ui.render')
        return { text: `queue: ${index + 1} removed · ${stack.length} left` }
      }
      if (word === 'now') {
        const entry = stack[index]!
        const how = sendNow($, entry.id)
        $.ui.invalidate('ui.render')
        return { text: how === 'pushed' ? `queue: ${index + 1} goes into the turn` : `queue: ${index + 1} is first · sending` }
      }
      if (word !== 'edit') {
        const to = word === 'mv' ? indexArg(target) : index + (word === 'up' ? -1 : 1)
        if (to === null) return { text: `queue: /q mv <n> <m>, 1 to ${stack.length}` }
        if (!moveAt(index, to)) return { text: `queue: ${index + 1} is already ${to === index ? 'there' : to < 0 ? 'first' : 'last'}` }
        $.ui.invalidate('ui.render')
        return { text: `queue: ${index + 1} is now ${to + 1}` }
      }
      const entry = stack[index]!
      // the await is long enough for another prompt to have moved the entry
      // under the index, so the fill takes it out by id
      if (!(await fillFrom($, entry))) return { text: `queue: the prompt box is busy · ${index + 1} is still held` }
      return { text: `queue: ${index + 1} is in the prompt box` }
    }
    if (word === 'send') {
      if (stack.length === 0) return { text: 'queue: nothing held' }
      if (turnId) return { text: `queue: ${stack.length} waiting · they go when the turn ends` }
      send($)
      return { text: `queue: sending ${joined ? `all ${stack.length}` : `the first of ${stack.length}`}` }
    }
    if (word === 'help') return { text: 'queue: /q <text> · up <n> · down <n> · mv <n> <m> · now <n> · rm <n> · edit <n> · clear · send · status' }
    // anything else is the prompt to hold
    stack.push({ id: `e${++counter}`, text: e.args.trim(), at: Date.now() })
    $.ui.invalidate('ui.render')
    if (turnId) return { text: `queue: held · ${stack.length} waiting · sent when the turn ends` }
    if (inFlight > 0) return { text: `queue: held · ${stack.length} waiting · sent when the background work ends` }
    send($)
    return { text: `queue: nothing is running · sending${stack.length > 1 ? ` · ${stack.length} waiting` : ''}` }
  })

  on('ui.render', { component: 'AbovePrompt' }, async ($, e, next) => {
    if (e.surface !== 'terminal' || e.props.hasSurvey || stack.length + steer.length === 0) return next(e)
    // The backstop: a stack found idle goes out rather than sitting here. By
    // our own count of the turn alone: `isWorking` reads false while a tool
    // runs under the fullscreen renderer, so it cannot clear `turnId`. Deferred
    // past this dispatch, from which a submit would be refused.
    if (!turnId && inFlight === 0 && !e.props.isWorking && failures < RETRIES) armGate($)
    return bandOf($, e)
  })
}
