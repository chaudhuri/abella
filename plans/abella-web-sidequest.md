# Sidequest: proof feedback and checking controls

**Status:** agreed — implementation pending.

**Scope:** an independent UX sidequest for Abella Web. It does not change
`plans/abella-web/v4.md` while it is being designed. If implemented, the
main plan will get a short note in a later version.

## 1. Observations

### 1.1 Proof results are disconnected from the proof

Abella emits `system_message`s such as:

- `Proof completed`
- `Proof completed *** USING skip ***`
- `Proof ABORTED`
- `Proof NOT Completed.`

These currently appear in the **Messages** pane, detached from the
theorem they refer to. The user has to reconstruct which proof they
belong to, and the messages pane becomes a wall of low-value lifecycle
text. The proof outcome is most useful next to the final obligation, as
a conclusion to the proof the user just watched.

### 1.2 Ctrl-Enter checks one command too many

Current behaviour (`Session.processTo`) selects commands with:

```ts
command.from <= cursor
```

so a command whose first character is exactly at the cursor is checked.
With the cursor immediately before a command:

```text
!apply foo to bar.
```

`apply` is checked, although the user's cursor has not entered the
command. The desired rule is:

- cursor before the command or at its first character → **do not**
  check it;
- cursor anywhere inside the command → **do** check it.

Examples:

```text
!apply foo to bar.     -- apply is not checked
a!pply foo to bar.     -- apply is checked
apply foo to bar!.     -- apply is checked
```

In other words, a command is checked when
`command.from < cursor`, and the checked region may extend past the
cursor to the end of the command the cursor is inside.

### 1.3 Ctrl-Shift-Enter is not useful

The current blocking mode checks only commands with `command.to <
cursor`; it exists to avoid checking the command under the cursor. Under
the new Ctrl-Enter rule, that distinction is mostly redundant and is
contradicted by the desired "cursor inside the command" behaviour. No
user-facing use case for blocking mode has been identified.

**Decision:** remove blocking mode and Ctrl-Shift-Enter.

### 1.4 Stepping through commands

Checking one command at a time is useful while developing a proof.
Desired behaviour:

- next command: check the **next unchecked** command (or no-op at the
  end);
- previous command: uncheck the **last checked** command (or no-op
  with nothing checked);
- if the cursor is at the end of the checked region, these operations
  also move the cursor:
  - next moves the cursor to the end of the newly checked command;
  - previous moves the cursor to the start of the command being
    unchecked;
- if the cursor is **not** at the end of the checked region, the
  checked region changes but the cursor stays where it is. This allows
  inspecting an earlier part of a checked development while advancing
  or retreating the checked tip.

A single canonical key pair is preferred. The decided pair is
`Ctrl-]` / `Ctrl-[` (§4.7).

### 1.5 Ctrl-Enter should also retreat

Pressing Ctrl-Enter with the cursor already inside the checked region
should move the checked region back to the left of the cursor, exactly
as if the user had edited there. Today the only way to retreat is to
modify text in the checked region; that is not a clean way to inspect
or re-check an earlier point.

This makes Ctrl-Enter a two-way "set the checked region to the cursor"
operation: it advances when the cursor is at or beyond the tip, and
rewinds when the cursor is before the tip.

### 1.6 Jump to the checked tip

A separate command should put the cursor at the end of the checked
region and scroll it into view when it is outside the visible part of
the CodeMirror buffer. This is useful after stepping forward or
backward, or when inspecting a long file.

## 2. Goals

- Show proof outcomes in the Goal pane, directly below the last
  obligation, using Abella's exact message text.
- Make Ctrl-Enter move the checked tip to the cursor in either
  direction.
- Remove Ctrl-Shift-Enter/blocking mode.
- Add next/previous command checking with the cursor movement rules
  above.
- Add a jump-to-checked-tip command.
- Retire the always-visible Messages pane in favour of a collapsed
  output area for non-proof messages.

## 3. Non-goals

- Changing the worker protocol or the OCaml prover.
- Changing Abella's message strings or CLI output; they may be consumed
  by other tooling.
- Changing how the checked region is decorated.
- Undo/redo of *text* (CodeMirror history), which remains separate.
- Autocomplete, hover types, or proof-state history.
- Rewriting the command scanner.

## 4. Design

### 4.1 Proof outcomes in the Goal pane

Add a proof outcome to the session model:

```ts
type ProofOutcome = {
  theorem?: string;
  status: "completed" | "completed-skip" | "aborted" | "not-completed";
  message: string;
};
```

The outcome is derived from the `system_message`s returned by a command:

| Message | Status |
| --- | --- |
| `Proof completed` | `completed` |
| `Proof completed *** USING skip ***` | `completed-skip` |
| `Proof ABORTED` | `aborted` |
| `Proof NOT Completed.` | `not-completed` |

The theorem name comes from the most recent `proof_command.theorem`
field (or from a preceding `Theorem` top command when no proof command
has run yet). Abella's completion message itself does not carry the
name.

The Goal pane renders:

1. the last sequent/obligation (unchanged, as a reminder);
2. below it, a separate theorem label (when known) and Abella's
   unchanged message, for example:

   ```text
   Theorem app_total
   Proof completed
   ```

   The message is displayed verbatim. The theorem label is separate UI
   text, not a rewrite of Abella's message. Aborted and failed proofs
   use the error colour.

The outcome is cleared when the checked region starts a new theorem or
is rewound before the completion. Implementation-wise, attach the
outcome to the `Step` that produced it and, on rewind, use the latest
outcome among the remaining steps (or none).

### 4.2 Messages pane disposition

**Decision:** remove the always-visible Messages pane and keep a small,
collapsed **Output** disclosure in the Goal pane.

Reason: not all non-proof messages are disposable. In particular:

- errors (also shown as lint diagnostics);
- warnings (`Warning: overriding existing lemma`, well-formedness
  warnings);
- import/specification progress;
- `Show` output;
- `Query` / `search` output (`Found solution`, `No more solutions`).

If the pane is removed without an alternative, `Show`, `Query`, and
warnings silently disappear. The proposed layout is:

```text
Goal
┌─────────────────────────────────────────────────────────────┐
│ Variables: ...                                              │
│ H1: ...                                                     │
│ =========================================                   │
│ goal                                                        │
│                                                             │
│ Theorem app_total                                           │
│ Proof completed                                             │
│ ▸ Warnings and output (3)                                   │
└─────────────────────────────────────────────────────────────┘
```

- The disclosure is collapsed by default.
- It opens automatically for errors and warnings, and when `Show` or
  `Query` produces output.
- Proof lifecycle messages never go into it.
- Errors are still shown through the existing lint diagnostics and the
  status badge.

### 4.3 Ctrl-Enter

Ctrl-Enter becomes a two-way "set the checked region to the cursor"
operation.

```text
if cursor < tip:
    rewindToLeftOf(cursor)   // drop steps with to > cursor
    return

commands = scanCommands(rootText, tip)
process commands with command.from < cursor
```

The forward rule replaces the current filter:

```ts
// before
blocking ? command.to < cursor : command.from <= cursor

// after
command.from < cursor
```

Consequences:

- At the start of a command, that command is not checked.
- Inside a command, the whole command is checked, so the checked tip
  may end past the cursor (through the terminating dot).
- In the whitespace between commands, the checked tip stops at the end
  of the previous command.

When the cursor is already inside the checked region, Ctrl-Enter only
rewinds; it does **not** immediately re-check the command under the
cursor. The checked region must end to the left of the cursor, so keep
only steps whose `to <= cursor` and drop every later step. The new tip
is the terminating dot of the last kept command (or 0 if none):

- checked through C, cursor inside B → undo B and C, tip = A.to (or 0);
- checked through C, cursor between B and C → undo C, tip = B.to;
- checked through C, cursor at the start of B → undo B and C,
  tip = A.to (or 0);
- cursor exactly at B.to → B stays checked, tip = B.to.

This is a boundary-of-commands rewind, not the edit rewind used by
`rewindTo`: an edit at an offset uses that offset as the new tip, while
Ctrl-Enter must stop at the last command that ends at or before the
cursor. The cursor does not move during this rewind. Pressing Ctrl-Enter
again then checks forward from the new tip, so the user can deliberately
re-check the command containing the cursor.

The processed-region decoration uses `tip = command.to`, so it may
extend past the visible cursor when the cursor is inside a command.

### 4.4 Remove blocking mode and Ctrl-Shift-Enter

**Decision:** remove them now.

Changes:

- delete the `blocking` parameter from `Session.processTo` and
  `processToCursor`;
- remove the `Mod-Shift-Enter` keybinding;
- remove the blocking hint from the footer;
- update the fake-driver tests and browser smoke test.

A future "check complete commands only" mode can be reintroduced
explicitly if a real use case appears.

### 4.5 Jump to the checked tip (`Ctrl-.`)

Add a cursor command, bound to `Ctrl-.` exactly (not `Mod-.`, so it is
Control on every platform):

1. If another file is active, switch to the root reasoning file.
2. Set the root editor selection to `tip` (the first unchecked offset).
3. Scroll that position into view, even if it is outside the visible
   part of the buffer (`EditorView.scrollIntoView(tip, { y: "center" })`
   or equivalent).
4. Focus the editor.
5. Do not change the checked region or the prover state.

If `tip` is 0, this moves to the start of the root file. The operation
is purely a cursor/scroll movement.

### 4.6 Next/previous command

Add two session operations (bindings discussed in §4.7):

```ts
stepForward(): Promise<void>
stepBackward(): Promise<void>
```

Definitions:

- **End of checked region:** `cursor >= tip`. This treats the cursor
  sitting in trailing whitespace after the checked region as "at the
  end" too.
- **Next unchecked command:** the first command returned by
  `scanCommands(rootText, tip)`. There is no next command when the scan
  returns an empty list.

`stepForward`:

1. If the cursor is at the end of the checked region, process exactly
   the next unchecked command; on success, move the cursor to
   `command.to`.
2. Otherwise process exactly that command but leave the cursor alone.
3. If there is no next command, do nothing.
4. On a processing error, leave the cursor alone and show the existing
   diagnostic.

`stepBackward`:

1. If there are no checked steps, do nothing.
2. Let `last` be the final step. Restore the previous prover state with
   `driver.back(1)`, drop the step, and set `tip = last.from`.
3. If the cursor was at the end of the checked region
   (`cursor >= oldTip`), move it to `last.from`; otherwise leave it
   alone.
4. Recompute the Goal state and proof outcome from the remaining steps.

Edge cases:

- If the checked region is empty, `tip = 0`; previous is a no-op.
- Repeated "previous" with the cursor at the end walks backwards one
  command at a time.
- Repeated "next" with the cursor before the tip advances the checked
  region without moving the cursor.
- If a spec/imported file was edited, the session is dirty; a step
  operation initializes first, which clears the steps and tip. The
  cursor remains wherever it was.

### 4.7 Keybindings

| Action | Binding | Notes |
| --- | --- | --- |
| Check to cursor / rewind to cursor | `Ctrl/Cmd-Enter` | Two-way; `command.from < cursor` rule |
| Next command | `Ctrl-]` | Decided canonical pair |
| Previous command | `Ctrl-[` | Decided canonical pair |
| Jump to checked tip | `Ctrl-.` | Control-dot on every platform |

Each of the user's suggested alternatives has a concrete conflict:

- `Ctrl-f` is already CodeMirror search (`searchKeymap`); taking it would
  break Find.
- `Ctrl-b` is browser bookmarks in Chromium/Firefox; intercepting it is
  surprising even if possible.
- `Ctrl-Right`/`Ctrl-Left` are word-wise cursor movement in CodeMirror
  and most editors; overloading them would break normal editing.
- `Ctrl-n`/`Ctrl-p` are browser new-window/print on Windows and Linux.

`Ctrl-]` / `Ctrl-[` avoid browser and CodeMirror search conflicts. They
are bound to indent more/less by CodeMirror's `defaultKeymap`, but Tab
and Shift-Tab already cover indentation, so the override is cheap. Bind
them as literal `Ctrl` (not `Mod`): `Cmd-[` is "back" in some browsers.

`Ctrl-.` is bound as literal `Ctrl-.` to match the request. If a
platform needs a different key later, it should still be a single
canonical pair, documented in the footer.

## 5. Implementation map

- `support/ts/web/session.ts`
  - replace the `blocking` filter with `command.from < cursor`;
  - make Ctrl-Enter rewind when `cursor < tip`, using a command-boundary
    rewind (`rewindToLeftOf`) rather than the edit rewind;
  - add `ProofOutcome`, `Step.outcome`, `stepForward`,
    `stepBackward`, and cursor-at-tip logic;
  - recompute outcomes on rewind/reset;
  - route non-proof messages to a separate output callback.
- `support/ts/web/main.ts`
  - remove the Messages pane;
  - render the outcome below the Goal sequent using Abella's raw text;
  - implement the Output disclosure;
  - add next/previous and jump-to-tip handlers and cursor updates;
  - remove `Ctrl-Shift-Enter`.
- `support/ts/web/editor.ts`
  - bind `Ctrl-]`/`Ctrl-[` and `Ctrl-.` in the editor keymap;
  - expose cursor-setting and scroll-into-view helpers.
- `web/index.html`, `support/css/web.css`
  - remove the Messages panel; make Goal full width;
  - add outcome and Output styles;
  - update footer hints.
- `support/ts/web/session.test.ts`
  - boundary tests for `from < cursor`;
  - undo-on-Ctrl-Enter tests, including the cursor staying put;
  - fake-driver tests for forward/backward with and without cursor
    movement;
  - outcome extraction and rewind invalidation.
- Browser smoke test
  - check the outcome appears in the Goal pane;
  - check messages pane absence;
  - exercise Ctrl-Enter in both directions and the stepping keys;
  - check `Ctrl-.` scrolls a tip outside the viewport into view.

## 6. Test plan

Unit (fake driver):

- cursor at `command.from` excludes the command;
- cursor inside the command includes it;
- Ctrl-Enter with the cursor inside the checked region rewinds to the
  last command ending at or before the cursor;
- cursor in the whitespace between two checked commands leaves the tip
  at the previous command's dot;
- cursor at the first character of a checked command leaves the tip at
  the previous command's dot;
- Ctrl-Enter does not immediately re-check after rewinding;
- a second Ctrl-Enter then checks forward;
- next at the end checks the next command and moves the cursor;
- next before the tip checks without moving the cursor;
- previous at the end unchecks one command and moves the cursor to its
  start;
- previous before the tip unchecks without moving the cursor;
- no-op at the beginning/end;
- proof outcome extraction for completed/skipped/aborted, preserving
  Abella's raw message;
- outcome cleared when the completion step is rewound;
- errors do not move the cursor;
- jump-to-tip requests the correct cursor position and scroll.

Browser:

- process `hh_meta` and verify the Goal pane shows `Proof completed`
  verbatim, under the last obligation, with a separate theorem label;
- verify no always-visible Messages pane;
- check Ctrl-Enter at `!apply` vs `a!pply`;
- check Ctrl-Enter with the cursor in the checked region rewinds;
- step with `Ctrl-]`/`Ctrl-[` and check cursor positions;
- check `Ctrl-.` scrolls a tip outside the viewport into view;
- edit before the tip and verify outcome/tip reset correctly;
- verify `Show` output still has a home;
- run the existing examples/zip/persistence smoke checks.

## 7. Cleanup

- Delete the Messages pane markup, CSS, and event plumbing.
- Remove `blocking` from the session API, tests, buttons, and hints.
- Update the footer keyboard hints.
- Keep the Output disclosure for non-proof messages, using the existing
  safe `system_message` renderer (`textContent`, severity attribute).
- No worker/adapter changes are expected.

## 8. Decisions

Settled:

- Keep a collapsed Output area for non-proof messages.
- Remove Ctrl-Shift-Enter and blocking mode.
- Ctrl-p leaves the cursor at the start of the unchecked command.
- Do not change Abella's message strings or CLI output.
- `Ctrl-.` jumps to the checked tip and scrolls it into view.
- Ctrl-Enter rewinds when the cursor is inside the checked region.
- `Ctrl-]` / `Ctrl-[` are the next/previous command bindings.
- `cursor >= tip` counts as "at the end of the checked region", so
  trailing whitespace still works with the stepping commands.
- Ctrl-Enter stops after rewinding; a second press checks forward.
- The theorem label appears above Abella's verbatim message, e.g.
  `Theorem app_total` followed by `Proof completed`.
- Starting a new, incomplete theorem hides the previous theorem's
  outcome.

There are no open design questions.

## 9. Exit criteria

- Proof completion/abort messages appear in the Goal pane under the
  last obligation, with a separate theorem label and Abella's exact
  message text.
- No always-visible Messages pane remains; the collapsed Output area
  holds warnings, errors, import progress, `Show`, and `Query`.
- Ctrl-Enter advances with `command.from < cursor` and rewinds when the
  cursor is in the checked region.
- Ctrl-Shift-Enter/blocking mode is removed.
- `Ctrl-]`/`Ctrl-[` step the checked region with the specified cursor
  movement.
- `Ctrl-.` moves to the checked tip and scrolls it into view.
- Unit and browser smoke tests pass.
- The main abella-web plan gets a short note only after implementation.
