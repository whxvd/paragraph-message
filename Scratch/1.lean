import MPiL.Util
import Qq
import Lean.Widget.InteractiveDiagnostic
open Lean Qq

#check Widget.msgToInteractive

deriving instance Repr for Std.Format.FlattenBehavior
deriving instance Repr for Std.Format

namespace Std.Format

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

namespace Lean.MessageData

def format' (msg : MessageData) : MetaM Format := do
  msg.format (ctx? := some ⟨← getEnv, ← getMCtx, ← getLCtx, ← getOptions⟩)

def join (l : List MessageData) : MessageData :=
  l.foldl (init := .nil) (· ++ ·)

def line : MessageData := .ofFormat .line

def text : String → MessageData := .ofFormat ∘ .text

def breakSpaces (s : String) : MessageData :=
  joinSep (toMessageData <$> s.splitOn " ") line

def inline : MessageData → MessageData := indentD ∘ group

def inline₂ (m : MessageData) : MessageData :=
  .nestD <| .group <| .ofFormat .line ++ m

def inline₁ (m : MessageData) : MessageData :=
  .group <| (.nestD <| .ofFormat .line ++ m) ++ .ofFormat .line

end Lean.MessageData

run_meta
  let e : Expr := q(∀ α _ _ _: Type, DecidableEq α)
  let msg : MessageData := .fill <| .join [
    .text "The", .line, .text "instance", .line, .text "hypothesis",
    .line, toMessageData e, .text ".", .line,
    .text "is", .line, .text "in", .line,
    .breakSpaces "violation of the lorem" ++
    .breakSpaces " ipsum dolor sit amet linter." ++
    .breakSpaces " Please change it immediately."]
  let fmt ← msg.format'
  -- logInfoAt here <| msg
  logInfoAt here <| fmt.pretty (width := 45)

run_meta
  let e : Expr := q(∀ α _ : Type, DecidableEq α)
  let msg : MessageData := .fill <|
    .breakSpaces "The instance hypothesis" ++ .inline₁ (e) ++
    .breakSpaces "is in violation of the lorem" ++
    .breakSpaces " ipsum dolor sit amet linter." ++
    .breakSpaces " Please change it immediately."
  let fmt ← msg.format'
  -- logInfoAt here <| msg
  logInfoAt here <| fmt.pretty (width := 45)

def aDo : Q(Id Nat) := q(do let a ← pure 0; pure (a + 0))

run_meta assert! (← (aDo |> toMessageData).format').hasHardLineBreak

variable {α : Type} [ToMessageData α] in
def logFormat (a : α) : MetaM Unit := do
  let f ← (toMessageData a).format'
  logInfo <| repr <| f.eraseTags

run_meta logFormat aDo

namespace Lean.MessageData

inductive ParagraphElement
  /--
  An unbreakable chunk of text
  -/
  | text (s : String)

  /--
  An inline message. May actually turn out not inline when it would not fit. An
  inline message always has an implicit soft break already at the start, but
  none at the end, just like, and for the same reasons as `Lean.indentD` has an
  `Std.Format.line` at the beginning, but not at the end.
  -/
  | inline (m : MessageData)

  /--
  A soft line break
  -/
  | line

def Paragraph := List ParagraphElement

/--
Normalize soft breaks: collapse multiple soft breaks into single ones, strip
leading and trailing ones.
-/
def Paragraph.normalize (p : Paragraph) : Paragraph :=
  match loop p with
    | .line :: es => es
    | es => es
where
  loop : Paragraph → Paragraph
    | []                        => []
    | [.line]                   => []
    | .line :: .line :: es      => loop (.line :: es)
    | .line :: .inline m :: es  => loop (.inline m :: es)
    | e :: es                   => e :: loop es

def ofParagraph (p : Paragraph) : MessageData :=
  let m := p.normalize.foldl (init := .nil) (· ++ match · with
    | .text s => .ofFormat (.text s)
    | .inline m => .inline m
    | .line => .ofFormat .line)
  .fill <| m ++ "\n"

instance: Append Paragraph := ⟨List.append⟩
instance: HAppend ParagraphElement ParagraphElement Paragraph := ⟨([·,·])⟩
instance: HAppend ParagraphElement Paragraph Paragraph := ⟨List.cons⟩
instance: HAppend Paragraph ParagraphElement Paragraph := ⟨List.concat⟩

/--
Turn a `String` into a paragraph by turning any whitespace into soft line breaks
-/
def Paragraph.ofString (s : String) : Paragraph :=
  let l : List ParagraphElement :=
    (s.split Char.isWhitespace).toList
    |>.filter (not ·.isEmpty)
    |>.map (.text ·.copy)
    |>.foldl (init := []) (· ++ [·, .line])
  if s.startsWith Char.isWhitespace then .line :: l else l

/--
Turn a `String` into a paragraph with a single unbreakable "word"
-/
def Paragraph.ofStringNoWrap : String → Paragraph := ([.text ·])

#check Lean.termM!_

macro:max "pm!" s:interpolatedStr(term) : term => do
  s.expandInterpolatedStr (← `(Paragraph))
    (ofInterpFn :=← `(ParagraphElement.inline))
    (ofLitFn :=← `(Paragraph.ofString))

run_meta logInfo <| format <| (← `(m!"abc {(23 : Nat)}"))

instance: Repr ParagraphElement where
  reprPrec e _ := match e with
    | .line => .text "line"
    | .text s => .text s!"text {s.quote}"
    | .inline _ => .text "inline"

instance: Repr Paragraph := inferInstanceAs (Repr (List ParagraphElement))

run_meta logInfo <| repr <| Paragraph.ofString "a b"

run_meta
  let e : Expr := q(∀ α _ _ _ _: Type, DecidableEq α)
  let p := pm!"
    The instance hypothesis {.sbracket e} is in violation of the lorem
    ipsum dolor sit amet linter. Please change it immediately."
  -- let p := pm!"a {.sbracket e} b"
  -- logInfoAt here (repr p.normalize)
  let m : MessageData := .ofParagraph p
  let fmt ← m.format'
  -- logInfoAt here <| msg
  logInfoAt here <| fmt.pretty (width := 45)

deriving instance Repr for Paragraph

end Lean.MessageData
