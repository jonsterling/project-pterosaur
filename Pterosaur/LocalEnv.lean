import Pterosaur.Bwd
import Pterosaur.Term
import Pterosaur.Value
import Pterosaur.Quote
import Pterosaur.Conv

structure LocalEnv (n : Nat) where
  types : Bwd Value n
  values : Bwd Value n
  names : Bwd String n

def LocalEnv.empty : LocalEnv 0 :=
  ⟨{},{},{}⟩

instance : EmptyCollection (LocalEnv 0) where
  emptyCollection := LocalEnv.empty

def LocalEnv.ext (Γ : LocalEnv n) (name : Option String) (A : Value) (a : Value) : LocalEnv (n+1) :=
  {types := Γ.types ⬝ A,
   values := Γ.values ⬝ a,
   names := Γ.names ⬝ Option.getD name "_anon"}

def Sequent.quote (𝕋 : Theory) : {n : Nat} → (Γ : LocalEnv n) → (B : Term n) → Term 0
| 0, _, B => B
| _+1, ⟨Γ⬝A, γ⬝_, ρ⬝nm⟩, B =>
  Sequent.quote 𝕋 ⟨Γ,γ,ρ⟩ $ Term.prod nm (A.quote 𝕋) B
