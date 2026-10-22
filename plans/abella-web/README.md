# Abella Web plan

**Latest version:** [v2](v2.md) — 2026-10-22

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
