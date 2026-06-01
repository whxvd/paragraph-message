import Paragraph
import Debug
import Lean
import Qq
open Lean Qq
open MessageData (Paragraph)

-- Delaboration of, e.g., `do` syntax creates hard line breaks. That cannot
-- really appear inline in a paragraph. It must always fall back to a separate
-- block.
def d : Q(Id Nat) := q(do let a ← pure 0; pure (a + 0))
run_meta assert! (← (toMessageData d).format').hasHardLineBreak
/--
info: do
  let a ← pure 0
  pure (a + 0)
-/
#guard_msgs in run_meta logInfo d

-- Two expressions that contain only soft breaks.
def e₀ : Expr := q(∀ α: Type, DecidableEq α)
def e₁ : Expr := q(∀ α _ _ _ _: Type, DecidableEq α)
run_meta assert! not (← (toMessageData e₀).format').hasHardLineBreak
run_meta assert! not (← (toMessageData e₁).format').hasHardLineBreak

def p₀ : Paragraph := pm!"
  The instance hypothesis {.sbracket e₀} is in violation of the lorem
  ipsum dolor sit amet linter. Please change it immediately.
"

def p₁ : Paragraph := pm!"
  The instance hypothesis {.sbracket e₁} is in violation of the lorem
  ipsum dolor sit amet linter. Please change it immediately.
"

-- The expression fits on its line, so it is inline:

/--
info: The instance hypothesis [(α : Type) → DecidableEq α] is in
violation of the lorem ipsum dolor sit amet linter. Please
change it immediately.
-/
#guard_msgs in run_meta logInfo <|← Paragraph.pretty (width := 60) pm!"
  The instance hypothesis {.sbracket e₀} is in violation of the lorem
  ipsum dolor sit amet linter. Please change it immediately.
"

-- The expression does not fit anymore, so

/--
info: The instance hypothesis
[(α : Type) → DecidableEq α] is in violation
of the lorem ipsum dolor sit amet linter.
Please change it immediately.
-/
#guard_msgs in run_meta logInfo <|← Paragraph.pretty (width := 45) pm!"
  The instance hypothesis {.sbracket e₀} is in violation of the lorem
  ipsum dolor sit amet linter. Please change it immediately.
"

/--
info: The instance hypothesis
[(α : Type) → Type → Type → Type → Type → DecidableEq α] is in
violation of the lorem ipsum dolor sit amet linter. Please change
it immediately.
-/
#guard_msgs in run_meta logInfo <|← Paragraph.pretty (width := 65) pm!"
  The instance hypothesis {.sbracket e₁} is in violation of the lorem
  ipsum dolor sit amet linter. Please change it immediately.
"

/--
info: The instance hypothesis
[(α : Type) →
   Type → Type → Type → Type → DecidableEq α]
is in violation of the lorem ipsum dolor sit
amet linter. Please change it immediately.
-/
#guard_msgs in run_meta logInfo <|← Paragraph.pretty (width := 55) pm!"
  The instance hypothesis {.sbracket e₁} is in violation of the lorem
  ipsum dolor sit amet linter. Please change it immediately.
"

/--
info: The instance hypothesis
(α : Type) → DecidableEq α is in violation of
the lorem ipsum dolor sit amet linter. Please
change it immediately.
-/
#guard_msgs in run_meta logInfo <|← Paragraph.pretty (width := 45) pm!"
  The instance hypothesis {e₀} is in violation of the lorem
  ipsum dolor sit amet linter. Please change it immediately.
"

/--
info: A B
do
  let a ← pure 0
  pure (a + 0)
C D.
-/
#guard_msgs in run_meta logInfo <|← Paragraph.pretty (width := 45) pm!"
  A B {d} C D.
"
