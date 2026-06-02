import Lean import Qq open Lean Qq

def Std.Format.paragraphify (s : String) : Format := .joinSep (s.splitOn " ") .line

def Lean.MessageData.paragraphify : String → MessageData := .ofFormat ∘ .paragraphify
def Lean.MessageData.line : MessageData := .ofFormat .line

def Lean.MessageData.format' (msg : MessageData) : MetaM Format := do
  msg.format (ctx? := some ⟨← getEnv, ← getMCtx, ← getLCtx, ← getOptions⟩)

/--
info: The instance hypothesis
(α : Type) →
  Type →
    Type →
      Type →
        Type → Type → Type → DecidableEq α
is in violation of the lorem ipsum dolor sit
amet linter. Please change it immediately.
-/
#guard_msgs (whitespace := exact) in
run_meta do
  let e := q(∀ α _ _ _ _ _ _ : Type, DecidableEq α)
  let msg : MessageData := .paragraphify "The instance hypothesis" ++ .line ++
    m!"{e}" ++ .line ++ .paragraphify "is in violation of the lorem" ++ .line ++
    .paragraphify "ipsum dolor sit amet linter. Please change it immediately."
  let fmt : Format := .group (behavior := .fill) <|← msg.format'
  logInfo <| fmt.pretty (width := 45)
