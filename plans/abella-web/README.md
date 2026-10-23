# Abella Web plan

**Latest version:** [v9](v9.md) — 2026-10-23

This directory contains the versioned design plan for Abella Web, the
browser interface for Abella.

## Versioning policy

- Each substantive revision is published as a new file `vN.md`. A
  published version is immutable for substantive content; typo and
  formatting fixes are the only exception, and are logged.
- The latest version is the source of truth; older versions are kept for
  history.
- Scope changes, design changes, and new decisions require a new version
  and an entry in the version log below.
- Typo-only or formatting corrections may be folded into the current
  version, but must still be recorded in the version log and commit
  history.
- Commits that change the plan should name the plan version they
  produce.

To publish a new version:

1. Copy the latest `vN.md` to `vN+1.md`.
2. Apply the changes and update the version header/date.
3. Add a row to the version log and update the “Latest version” line.
4. Commit with a message such as
   `docs(plan): publish Abella Web plan vN+1`.

## Version log

| Version | Date | Summary |
| --- | --- | --- |
| [v1](v1.md) | 2026-10-22 | Initial plan: static client-side prover, Phase 0 js_of_ocaml/wasm_of_ocaml bake-off, Web Worker, multi-file projects with imports, in-browser `.thc` session cache, zip interchange, non-Abella text files, plain CSS, timeboxed local-directory support, GitHub-first workspace design, and PAT-first authentication. |
| [v2](v2.md) | 2026-10-22 | Phase 0 complete: both backends built from one adapter; **wasm_of_ocaml selected** (~2.3× faster on CCS, comparable artifact size); records measured results, FFI conversion rules, `application/wasm`/CSP requirements, wasm worker placement, and Dune >= 3.20. |
| [v3](v3.md) | 2026-10-22 | Phase 1 complete: native OUnit coverage for virtual sources, output collection, generated/native `.thc` comparison, `.thc` fast path, nested imports, cycles, and missing files; documents the prover reset contract and canonical import progress names. |
| [v4](v4.md) | 2026-10-22 | Phase 2 complete: CodeMirror 6 UI, project sidebar, worker driver, command scanner and session tests, `abella_bundle` with eight curated examples, zip import/export, localStorage persistence, and goal/message panels; headless Chromium smoke test passes the full exit criterion. |
| [v5](v5.md) | 2026-10-22 | Checking/feedback sidequest: proof outcomes and theorem labels in the Goal pane, Messages pane replaced by a collapsed Output disclosure, two-way Ctrl-Enter, `Ctrl-]`/`Ctrl-[` stepping, `Ctrl-.` jump to tip, and removal of blocking mode. |
| [v6](v6.md) | 2026-10-23 | Phase 3 UX complete: file add/rename/delete and root selection, worker Stop, destructive-action/save warnings, accessibility pass, responsive goal scrolling, resizable sidebar, and Howe replacing CCS in the curated examples. |
| [v7](v7.md) | 2026-10-23 | Phase 3b complete: best-effort Chromium local-directory backend with feature-detected Open folder, recursive project read, dirty markers, Save/Save all, permission and external-modification handling; IndexedDB reopen deferred and structural file actions disabled in folder mode. |
| [v8](v8.md) | 2026-10-23 | Phase 4 repository hardening: bounded 64 MiB `.thc` cache, lazy-loaded Markdown chunk, asset-size budgets, web CI workflow, build/deploy docs, and cross-browser Chromium/Firefox/WebKit smoke coverage; real-origin deployment and external link update remain. |
| [v9](v9.md) | 2026-10-23 | Phase 5 complete: `Workspace` interface with capabilities and typed errors, `WorkspaceSession`, virtual/directory/read-only-memory backends, IndexedDB folder reattach with detached-copy fallback, topbar workspace control, and directory structural actions left disabled. |
