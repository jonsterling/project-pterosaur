import Pterosaur.RefinerTypes

variable [Monad m] [MonadState Theory m] [MonadExcept String m]

def ValueSynthesiser.fail (msg : String) : ValueSynthesiser m n :=
  λ _ => throw msg

def TermChecker.fail (msg : String) : TermChecker m n :=
  λ _ _ => throw msg

def CoerceTerm.shift : CoerceTerm m n :=
  λ Γ ⟨M0, C0, C1⟩ => do
  convert Γ C0 C1
  let 𝕋 ← get
  return .identity $ Thunk.mk λ _ =>
  M0.quote 𝕋

def ValueSynthesiser.coerce (focus : ValueSynthesiser m k) (coe : CoerceTerm m k) : TermChecker m k :=
  fun Γ type => do
  let hyp ← focus Γ
  let result ← coe Γ ⟨hyp.value, hyp.type, type⟩
  return result.get

def checkHole (name : String) : TermChecker ElabM n :=
  λ Γ C => do
  let 𝕋 ← get
  let holeType := Sequent.quote 𝕋 Γ (C.quote 𝕋)
  let vholeType := holeType.eval 𝕋 {}
  let holeName := Name.mk $ {} ⬝ .machine "hole" ⬝ .user name
  let format : Std.Format := .group $ f!"?{holeName}" ++ " :" ++ .nest 2 (.line ++ holeType.format {} 0);
  IO.println format
  MonadState.set $ 𝕋.insertGlobal holeName $ .abstract vholeType
  return plugLocalVarSpine (.globalVar holeName) (buildLocalVarSpine n)

def quoteCheckValue (tac : ValueChecker m n) : TermChecker m n :=
  λ Γ sort => do
  let V ← tac Γ sort
  return V.quote (← get)

def evalCheckTerm (tac : TermChecker m n) : ValueChecker m n :=
  λ Γ sort => do
  let term ← tac Γ sort
  return term.eval (← get) Γ.values

def ascribe (tacA : ValueChecker m n) (tacM : ValueChecker m n) : ValueSynthesiser m n :=
  λ Γ => do
  let A ← tacA Γ .TYPE
  let M ← tacM Γ A
  return {value := M, type := A}

def hypothesis (hypo : Defined) : ValueSynthesiser m n :=
  λ _ => return hypo

def weaken (tac : ValueSynthesiser m n) : ValueSynthesiser m (n+1) :=
  λ ⟨Γ⬝_, γ⬝_, names⬝_⟩ => tac ⟨Γ, γ, names⟩


def reveal (name : Name) (tac : TermChecker m n) : TermChecker m n :=
  λ Γ type => do
  let mut 𝕋 ← get
  if name ∈ 𝕋.revelations then tac Γ type else
  MonadState.set {𝕋 with revelations := 𝕋.revelations.insert name}
  let result ← tac Γ type
  𝕋 ← get
  MonadState.set {𝕋 with revelations := 𝕋.revelations.erase name}
  return result
