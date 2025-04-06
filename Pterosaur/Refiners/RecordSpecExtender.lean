import Pterosaur.RefinerTypes

variable [Monad m] [MonadState Theory m] [MonadExcept String m]

namespace RecordSpecExtender

def identity : RecordSpecExtender m n :=
  λ _ ⟨_, Self⟩ => return Self

def require (selfName? : Option String) (ℓ : Name) (tacA : TermChecker m (n+1)) (tacM? : Option (TermChecker m (n+1))) : RecordSpecExtender m n :=
  λ Γ ⟨sort, Self⟩ => do
  if List.contains (Self.map Prod.fst) ℓ
  then throw s!"RecordSpec.require: duplicate method specification {ℓ}"
  let tpSelf := Value.rcdTp none selfName? Self
  let x := fresh n tpSelf
  let Γ' := Γ.ext selfName? tpSelf x
  let type ← tacA Γ' sort
  let manifest? ←
    tacM?.mapM λ tacM => do
    let vtype := type.eval (← get) Γ'.values;
    let term ← tacM Γ' vtype
    pure ⟨Γ.values, term⟩
  return Self ++ [⟨ℓ, ⟨Γ.values, type⟩, manifest?⟩]

def append (tac1 : RecordSpecExtender m n) (tac2 : RecordSpecExtender m n) : RecordSpecExtender m n :=
  λ Γ ⟨sort, Self⟩ => do
  let dict1 ← tac1 Γ ⟨sort, Self⟩
  tac2 Γ ⟨sort, dict1⟩

def splice (selfName? : Option String) (target : Name) (tacType : TermChecker m (n+1)) : RecordSpecExtender m n :=
  λ Γ ⟨sort, Self⟩ => do
  if List.contains (Self.map Prod.fst) target
  then throw s!"RecordSpec.splice: duplicate method specification {target}"
  let tpSelf := Value.rcdTp none selfName? Self
  let x := fresh n tpSelf
  let Γ' := Γ.ext selfName? tpSelf x
  let typex ← tacType Γ' sort
  let 𝕋 ← get
  let vtypex := typex.eval 𝕋 Γ'.values
  match vtypex.destructRcdTp with
  | none => throw s!"RecordSpec.splice: expected locale type"
  | some ⟨none, _, _⟩ => throw s!"RecordSpec.splice: expected locale type"
  | some ⟨locale?, innerSelf?, specx⟩ =>
    let purified := specx.purify

    let rec loop (Self : RecordSpec) : Closure.Dict → m RecordSpec
    | [] => do
      let fullManifest :=
        purified.partialManifest.append ∘ purified.methods.map $ λ ⟨ℓ,_⟩ =>
        ⟨ℓ, ⟨Γ'.values, .call (.localVar (.pop .top)) ℓ⟩⟩
      let refinedSumType := vtypex.refine 𝕋 innerSelf? specx fullManifest
      let tmRefinedSumType := refinedSumType.whnf.quote 𝕋
      let manifestObj := Value.obj locale? innerSelf? fullManifest []
      let tmManifestObj := manifestObj.quote 𝕋
      pure $ Self ++ [⟨target, ⟨⟨Γ.values, tmRefinedSumType⟩, some ⟨Γ.values, tmManifestObj⟩⟩⟩]

    | ⟨ℓ, A⟩ :: rest =>
      if List.contains (Self.map Prod.fst) ℓ
      then throw s!"RecordSpec.splice: duplicate method specification {ℓ}"
      else do loop (Self ++ [⟨ℓ, ⟨A, none⟩⟩]) rest

    loop Self purified.methods
