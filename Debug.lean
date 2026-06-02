import Lean
import Paragraph
open Lean

-- Helpers for introspection and debugging

namespace Std.Format

deriving instance Repr for Std.Format.FlattenBehavior
deriving instance Repr for Std.Format

def eraseTags : Format → Format
  | nest i f => nest i (eraseTags f)
  | append f₁ f₂ => append (eraseTags f₁) (eraseTags f₂)
  | group f b => group (eraseTags f) b
  | tag _ f => eraseTags f
  | f => f

def hasHardLineBreak (f : Format) : Bool :=
  hasLineWithoutGroup f || hasNewlineInText f
where
  hasLineWithoutGroup : Format → Bool
    | line => true | group _ _ => false
    | nil | align _ | text _ => false
    | nest _ f => hasLineWithoutGroup f
    | append f₁ f₂ => hasLineWithoutGroup f₁ || hasLineWithoutGroup f₂
    | tag _ f => hasLineWithoutGroup f
  hasNewlineInText : Format → Bool
    | text s => s.find? "\n" |>.isSome
    | nil | line | align _ => false
    | nest _ f => hasNewlineInText f
    | append f₁ f₂ => hasNewlineInText f₁ || hasNewlineInText f₂
    | group f _ => hasNewlineInText f
    | tag _ f => hasNewlineInText f

end Std.Format

namespace Lean.MessageData

/--
Turn `MessageData` into `Format` in `MetaM`.

With just `MessageData.format` and no context, `MessageData.ofExpr` (aka
`ToMessageData Expr`) uses `toString`.
-/
def format' (msg : MessageData) : MetaM Format := do
  msg.format (ctx? := some ⟨← getEnv, ← getMCtx, ← getLCtx, ← getOptions⟩)

instance: Repr ParagraphElement where
  reprPrec e _ := match e with
    | .line => .text "line"
    | .text s => .text s!"text {s.quote}"
    | .inline _ => .text "inline"

instance: Repr Paragraph := inferInstanceAs (Repr (List ParagraphElement))

def Paragraph.pretty (p : Paragraph) (width : Nat := 45) : MetaM String := do
  let m : MessageData := .ofParagraph p
  let f : Format ← m.format'
  return f.pretty (width := width)

end Lean.MessageData

variable {α : Type} [ToMessageData α] in
def logFormat (a : α) : MetaM Unit := do
  let f ← (toMessageData a).format'
  logInfo <| repr <| f.eraseTags
