import Pterosaur.RefinerTypes

namespace Connective.Universe
variable [Monad m] [MonadExcept String m]

-- inconsistent
def formation : TermChecker m n :=
  λ _ sort =>
  match sort.destructTYPE with
  | none => throw "Universe.formation: expected sort"
  | some () => return .TYPE
