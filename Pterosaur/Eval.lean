import Pterosaur.Prelude
import Pterosaur.Bwd
import Pterosaur.Term
import Pterosaur.Value
import Pterosaur.Theory

variable (𝕋 : Theory)


mutual
  partial
  def Term.eval (γ : Bwd Value n) : Term n → Value
  | .globalVar x =>
    match 𝕋.getBoundary x with
    | none => .error "eval: missing global var"
    | some boundary =>
      let neutral := ⟨ .globalVar x, {} ⟩
      .neu neutral boundary
  | .localVar i => Bwd.proj γ i
  | .lam name? A M => .lam name? (Thunk.mk λ _ => A.eval γ) ⟨γ, M⟩
  | .prod name? A B => .prod name? (A.eval γ) ⟨γ, B⟩
  | .app M N => Value.apply (M.eval γ) (N.eval γ)
  | .sum locale? selfName? methods => .sum locale? selfName? (methods.close γ)
  | .obj locale? selfName? manifest dict => .obj locale? selfName? (Term.Dict.close γ manifest) (Term.Dict.close γ dict)
  | .call M name => Value.call (M.eval γ) name
  | .refine M selfName? spec inst => Value.refine (M.eval γ) selfName? (spec.close γ) (inst.close γ)
  | .TYPE => .TYPE
  | .error msg => .error msg

  partial
  def Closure.inst (clo : Closure Value) (arg : Value) : Value :=
    clo.inside.eval $ clo.locals ⬝ arg

  partial
  def Frame.plug : Value → Frame Value → Value
  | .neu neu bdry, frm => .neu (frm.plugNeutral neu) (frm.plugBoundary neu bdry)
  | .lam _ _ clo, .appTo arg => clo.inst arg
  | self@(.obj locale? _ manifest dict), .call ℓ =>
    let extension? := do (← 𝕋.locales[(<- locale?)]?).extensions[ℓ]?;
    match (do (← extension?).impl) <|> manifest.lookup ℓ <|> dict.lookup ℓ with
    | some clo => clo.inst self
    | none => .error s!"Frame.plug: method `{ℓ}` not found"
  | .sum locale? selfName? spec, .refine _ _ inst =>
    .sum locale? selfName? $ spec.map λ ⟨ℓ, cell⟩ =>
    ⟨ℓ,
     match inst.lookup ℓ with
     | some clo => {cell with manifest? := some clo}
     | none => cell⟩
  | _, _ => .error "Frame.plug: invalid arguments"

  partial
  def Spine.plug : Value → Spine len → Value
  | V, .emp => V
  | V, .snoc spine frame =>
    let V' := Spine.plug V spine;
    Frame.plug V' frame


  partial
  def Frame.plugBoundary : Neutral Value → Boundary Value → Frame Value → Boundary Value
  | _, .translucent U, frm => .translucent $ U.map frm.plug
  | _, .abstract C, .appTo arg =>
    .abstract $ Thunk.mk λ _ =>
    match C.get.destructProd with
      | none => Value.error "Frame.plugBoundary: appTo expected pi type"
      | some ⟨_,_,B⟩ => B.inst arg
  | _, .abstract _, .refine _ _ _ =>
    .abstract $ Value.error "Frame.plugBoundary: ill-typed plugging of abstract value into 'refine' frame"
  | neu, .abstract C, .call ℓ =>
    let self := Value.neu neu (.abstract C)
    match C.get.destructRcd with
    | none =>
      .abstract $ Thunk.pure $
      Value.error s!"Frame.plugBoundary: expected sum type"
    | some ⟨locale?, _, spec⟩ =>
      let extension? := do (← 𝕋.locales[(<- locale?)]?).extensions[ℓ]?
      match extension? with
      | some extension =>
       .translucent $ Thunk.mk λ _ =>
        extension.impl.inst self
      | none =>
        match spec.lookup ℓ with
        | some ⟨_, some manifest⟩ =>
         .translucent $ Thunk.mk λ _ =>
         manifest.inst self
        | some ⟨B, none⟩ =>
        .abstract $ Thunk.mk λ _ => B.inst self
        | none =>
         .abstract $ Thunk.pure $
         Value.error s!"Frame.plugBoundary: method not found"

  partial
  def Value.apply (U V : Value) : Value :=
    Frame.plug U (.appTo V)

  partial
  def Value.call (U : Value) (name : Name) : Value :=
    Frame.plug U (.call name)

  partial
  def Value.refine (U : Value) (selfName? : Option String) (spec : RecordSpec) (inst : List (Name × Closure Value)) : Value :=
    Frame.plug U (.refine selfName? spec inst)
end
