import Lake
open Lake DSL

/-- Machine-checked contract spec for typed decision engines
(System 1 through System 1.5). Core Lean only — no Mathlib,
no external dependencies; `lake build` after `elan` installs
the pinned toolchain. -/
package «typed_decision» where

@[default_target]
lean_lib «TypedDecision» where
