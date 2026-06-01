import Lean
import Paragraph
open Lean

-- Just for introspection and debugging:

namespace Std.Format

deriving instance Repr for Std.Format.FlattenBehavior
deriving instance Repr for Std.Format

def eraseTags : Format → Format
  | nest i f => nest i (eraseTags f)
  | append f₁ f₂ => append (eraseTags f₁) (eraseTags f₂)
  | group f b => group (eraseTags f) b
  | tag _ f => eraseTags f
  | f => f

def hasHardLineBreak : Format → Bool
  | nil => false
  | line => false
  | align _ => false
  | text s => s.find? "\n" |>.isSome
  | nest _ f => hasHardLineBreak f
  | append f₁ f₂ => hasHardLineBreak f₁ || hasHardLineBreak f₂
  | group f _ => hasHardLineBreak f
  | tag _ f => hasHardLineBreak f

end Std.Format

variable {α : Type} [ToMessageData α] in
def logFormat (a : α) : MetaM Unit := do
  let f ← (toMessageData a).format'
  logInfo <| repr <| f.eraseTags

namespace Lean.MessageData

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
