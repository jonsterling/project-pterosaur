import Pterosaur.RefinerTypes

variable [Monad m] [MonadExcept String m]

-- inconsistent
def universeFormation : TermChecker m n :=
  λ _ sort =>
  match sort.destructTYPE with
  | none => throw "Universe.formation: expected sort"
  | some () => return .TYPE
