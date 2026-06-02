import Paragraph
import Debug
import Lean
import Qq
open Lean Qq
open MessageData (Paragraph)

-- Two expressions that contain only soft breaks, one longer than the other
def e₀ : Expr := q(∀ α: Type, DecidableEq α)
def e₁ : Expr := q(∀ α _ _ _ _: Type, DecidableEq α)
run_meta assert! ¬ (← (toMessageData e₀).format').hasHardLineBreak
run_meta assert! ¬ (← (toMessageData e₁).format').hasHardLineBreak

/--
info: The instance hypothesis [(α : Type) → DecidableEq α] is in
violation of the lorem ipsum dolor sit amet linter. Please
change it immediately.
-/
#guard_msgs (whitespace := exact) in
run_meta logInfo <|← Paragraph.pretty (width := 60) pm!"
  The instance hypothesis {.sbracket e₀} is in violation of the lorem
  ipsum dolor sit amet linter. Please change it immediately.
"

/--
info: The instance hypothesis
[(α : Type) → DecidableEq α] is in violation
of the lorem ipsum dolor sit amet linter.
Please change it immediately.
-/
#guard_msgs (whitespace := exact) in
run_meta logInfo <|← Paragraph.pretty (width := 45) pm!"
  The instance hypothesis {.sbracket e₀} is in violation of the lorem
  ipsum dolor sit amet linter. Please change it immediately.
"

/--
info: The instance hypothesis
[(α : Type) → Type → Type → Type → Type → DecidableEq α] is
in violation of the lorem ipsum dolor sit amet linter.
Please change it immediately.
-/
#guard_msgs (whitespace := exact) in
run_meta logInfo <|← Paragraph.pretty (width := 60) pm!"
  The instance hypothesis {.sbracket e₁} is in violation of the lorem
  ipsum dolor sit amet linter. Please change it immediately.
"

/--
info: The instance hypothesis
[(α : Type) →
   Type → Type → Type → Type → DecidableEq α]
is in violation of the lorem ipsum dolor sit amet
linter. Please change it immediately.
-/
#guard_msgs (whitespace := exact) in
run_meta logInfo <|← Paragraph.pretty (width := 55) pm!"
  The instance hypothesis {.sbracket e₁} is in violation of the lorem
  ipsum dolor sit amet linter. Please change it immediately.
"

-- Formatting of, e.g., `do` or `let` syntax creates hard line breaks. That
-- cannot really appear inline in a paragraph. It must always fall back to a
-- separate block.

def d : Q(Id Nat) := q(do let a ← pure 0; pure (a + 0))
run_meta assert! (← (toMessageData d).format').hasHardLineBreak

/--
info: A B
do
  let a ← pure 0
  pure (a + 0)
C D.
-/
#guard_msgs (whitespace := exact) in
run_meta logInfo <|← Paragraph.pretty (width := 1000) pm!"
  A B {d} C D.
"
