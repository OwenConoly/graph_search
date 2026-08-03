# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A Coq/Rocq 9.0 formalization of graph search (starting with `DFS.v`). Early stage — the sources are still being written. There is no test suite; compilation is verification. Built on top of the `coqutil` library (git submodule).

## Build

Submodules must be checked out first: `git submodule update --init --recursive`.

- `make` (= `make all`) — builds the `coqutil` prerequisite, then everything in this repo.
- Single file (preferred iteration loop; handles dependency order):
  `make -f Makefile.coq DFS.vo`
- `Makefile.coq` is generated from `_CoqProject` via `coq_makefile`; regenerate by deleting it and running `make`, or edit `_CoqProject` and `make` will rebuild it. Source roots map to logical names in `_CoqProject`: `coqutil/src/coqutil` → `coqutil`, and this repo's root → `GraphSearch`.

To compile a file directly without the Makefile, pass the same `-Q <dir> <Name>` mappings:

```
coqc -Q coqutil/src/coqutil coqutil -Q . GraphSearch DFS.v
```

Individual files compile fast (a couple of seconds each) — iterate with foreground `coqc`/`make -f Makefile.coq` rather than background builds. Check for incomplete proofs with `grep -rn "Admitted" .` (excluding `coqutil/`).

To search the compiled libraries for lemmas, write a scratch file containing `Require Import` + `Search ...` commands and compile it with the same `-Q` mappings:

```
coqc -Q coqutil/src/coqutil coqutil -Q . GraphSearch /tmp/search.v
```

To see proof state at a point in a batch `coqc` run, insert `Show.` into the proof script.

The `coqutil/` directory is a git submodule — don't edit it.

## Conventions

- Never change a theorem statement, `Context` hypothesis, or obligation definition to unblock a proof — ask first.
- New generic facts about maps/lists/folds belong in a shared util file (or upstream in `coqutil`), not inlined into the proof that needs them. Search `coqutil` for an existing lemma before proving one.
- State lemma variables as named binders before the colon (no `forall` in statements); drop inferable type annotations; destructure tuples with descriptive names.
- Leave at least one blank line before each `Definition`/`Lemma`/`Theorem`.
- Close arithmetic goals with `lia`; prefer the shortest tactic invocation that works.
- No dependently typed code (`eq_rect`, dependent `match` on equality proofs).
- Don't use `classic` / `Classical_Prop` (or any classical axiom) unless the user explicitly says it's okay. Decidable props (e.g. `In` over an `Eqb` type) can be case-split constructively with `existsb`/`in_dec` instead.
- Don't write comments about obvious things: no restating what a definition/lemma already says, no narrating Coq/section/`Arguments` mechanics, no justifying routine constructs. Comment only a genuinely non-obvious *why*, and keep it short. Default to no comment.
