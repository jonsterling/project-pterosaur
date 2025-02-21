import Pterosaur.RefinerTypes

variable [Monad m] [MonadState Theory m] [MonadExcept String m]

namespace Connective.Product

def formation (name? : Option String) (tacA : TermChecker m n) (tacB : TermChecker m (n+1)) : TermChecker m n :=
  λ Γ sort =>
  match sort.destructTYPE with
  | none => throw "Pi.formation expected sort"
  | some () => do
    let tmA ← tacA Γ sort
    let valA := tmA.eval (← get) Γ.values
    let x := fresh n valA
    let tmB ← tacB (Γ.ext name? valA x) sort
    return .prod name? tmA tmB

def introduction (name : String) (tacM : TermChecker m (n+1)) : TermChecker m n :=
  λ Γ sort =>
  match sort.destructProd with
  | none => throw "Product.introduction expected product type"
  | some ⟨_, A, B⟩ => do
    let x := fresh n A
    let 𝕋 ← get
    return .lam name (A.quote 𝕋) $ ← tacM (Γ.ext name A x) (B.inst 𝕋 x)

def elimination (tacM : ValueSynthesiser m n) (tacN : ValueChecker m n) : ValueSynthesiser m n :=
  λ Γ => do
  let M ← tacM Γ
  match M.type.destructProd with
  | none => throw "Product.elimination expected product type"
  | some ⟨_, valA, cloB⟩ => do
    let N ← tacN Γ valA
    let 𝕋 ← get
    let valBN := cloB.inst 𝕋 N
    return { value := Value.apply 𝕋 M.value N, type := valBN }

def coercion (coeA : CoerceTerm m (n+1)) (coeB : CoerceTerm m (n+1)) : CoerceTerm m n :=
  λ Γ ⟨M0, C0, C1⟩ =>
  match C0.destructProd, C1.destructProd with
  | some ⟨_, A0, B0⟩, some ⟨name1?, A1, B1⟩ => do
    let vx := fresh n A1
    let B1_x := B1.inst (← get) vx
    let ΓA1 := Γ.ext name1? A1 vx
    match ← coeA ΓA1 ⟨vx, A1, A0⟩ with
    | .identity _ =>
      let mut 𝕋 ← get
      let M0_x := Value.apply 𝕋 M0 vx
      let B0_x := B0.inst 𝕋 vx
      let result ← coeB ΓA1 ⟨M0_x, B0_x, B1_x⟩
      𝕋 ← get
      match result with
      | .identity _ =>
        return .identity $ Thunk.mk λ _ => M0.quote 𝕋
      | .expansion coe_M0_x =>
        return .expansion $ Term.lam name1? (A1.quote 𝕋) coe_M0_x
    | .expansion tcoe_x =>
      return .expansion $ ← do
      let mut 𝕋 ← get
      let vcoe_x := tcoe_x.eval 𝕋 ΓA1.values
      let M0_coe_x := Value.apply 𝕋 M0 vcoe_x
      let B0_coe_x := B0.inst 𝕋 vcoe_x
      let coe_body ← coeB ΓA1 ⟨M0_coe_x, B0_coe_x, B1_x⟩
      𝕋 ← get
      return Term.lam name1? (A1.quote 𝕋) coe_body.get
  | _, _ => throw "Prod.Coercion: expected product types"
