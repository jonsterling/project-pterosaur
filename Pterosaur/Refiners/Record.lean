import Pterosaur.RefinerTypes

variable [Monad m] [MonadState Theory m] [MonadExcept String m]

def localeFormation (locale : Name) (tac : RecordSpecRefiner m n) : ValueSynthesiser m n:=
  λ Γ => do
  let 𝕋 ← get
  match 𝕋.getLocaleSpec locale with
  | none =>
    throw s!"localeFormation: no locale named {locale}"
  | some spec => do
    let rspec ← tac Γ spec.spec
    let type := Value.rcdTp locale spec.selfName? rspec
    return ⟨type, .TYPE⟩

def recordFormation (selfName? : Option String) (tac : RecordSpecExtender m n) : TermChecker m n :=
  λ Γ sort =>
  match sort.destructTYPE with
  | none =>
    throw "recordFormation expected sort"
  | some () => do
    let tele ← tac Γ ⟨sort, []⟩
    return .rcdTp none selfName? $ tele.quote (← get) selfName?

def refineRecordType (tacType : ValueSynthesiser m n) (tacRefine : RecordSpecRefiner m n) : ValueSynthesiser m n :=
  λ Γ => do
  let type ← tacType Γ
  match type.value.destructRcdTp with
  | none =>
    let 𝕋 ← get
    let ttype := type.value.quote 𝕋
    throw s!"Sum.refine expected sum type but got {ttype.format Γ.names 0}"
  | some ⟨_locale?, selfName?, spec⟩ =>
    let rspec ← tacRefine Γ spec
    let updates :=
      rspec.filterMap λ ⟨ℓ, cell⟩ =>
      cell.manifest?.bind λ impl =>
      match spec.lookup ℓ with
      | some ⟨_, none⟩ => some ⟨ℓ, impl⟩
      | _ => none
    return {value := Value.refine (← get) type.value selfName? spec updates, type := .TYPE}

def recordIntro (tac : ObjectDictChecker m n) : TermChecker m n :=
  λ Γ type => do
  match type.destructRcdTp with
  | none =>
    let ttype := type.quote (← get)
    throw s!"recordIntro expected sum type but got {ttype.format Γ.names 0}"
  | some ⟨locale?, selfName?, spec⟩ =>
    let ⟨manifest, primary⟩ ← tac Γ spec
    return .obj locale? selfName? manifest primary

def recordElim (tac : ValueSynthesiser m n) (ℓ : Name) : ValueSynthesiser m n :=
  λ Γ => do
  let 𝕋 ← get
  let M ← tac Γ
  match M.type.destructRcdTp with
  | none => throw s!"recordElim: expected sum type"
  | some ⟨locale?, _selfName?, spec⟩ =>
    let nope := do
      let tspec := M.type.whnf.quote 𝕋
      throw s!"recordElim: could not find method `{ℓ}` on spec: {tspec.format Γ.names 0} / {(M.value.quote 𝕋).format Γ.names 0}"
    match locale?, spec.lookup ℓ with
    | _, some ⟨B, _⟩ =>  do
      return {
        value := Value.call 𝕋 M.value ℓ,
        type := B.inst 𝕋 M.value
      }
    | none, none => nope
    | some locale, none =>
      let 𝕋 ← get
      match do (← 𝕋.locales[locale]?).extensions[ℓ]? with
      | none => nope
      | some extension =>
        return {
          value := Value.call 𝕋 M.value ℓ,
          type := extension.type.inst 𝕋 M.value
        }

partial
def recordCoercion (coeMethod : CoerceTerm m n) : CoerceTerm m n :=
  λ Γ ⟨M0, C0, C1⟩ => do
  match C0.destructRcdTp, C1.destructRcdTp with
  | some ⟨locale0?, selfName0?, spec0⟩, some ⟨locale1?, selfName1?, spec1⟩ =>
    let rec loop (manifest0 primary0 manifest1 primary1 : Closure.Dict) : (spec0 spec1 : RecordSpec) → m (CoercionResult (Term.Dict (n+1) × Term.Dict (n+1)))
    | [], [] => do
      let 𝕋 ← get
      let thunk := Thunk.mk λ _ => ⟨manifest1.quote 𝕋 selfName1?, primary1.quote 𝕋 selfName1?⟩
      if locale0? == locale1?
      then return .identity thunk
      else return .expansion thunk.get
    | ⟨ℓ0, B0⟩ :: rest0, ⟨ℓ1, B1⟩ :: rest1 => do
      if ℓ0 != ℓ1
      then throw s!"Sum.coercion: mismatched methods in telescopes {ℓ0} vs {ℓ1}"
      else do
        let 𝕋 ← get
        let ℓ := ℓ0
        let self0 := .obj none selfName0? manifest0 primary0
        let self1 := .obj none selfName0? manifest1 primary1
        let B0self0 := B0.type.inst 𝕋 self0
        let B1self1 := B1.type.inst 𝕋 self1
        let M0_call := Value.call 𝕋 M0 ℓ
        let ⟨manifest0', self0'⟩ : Closure.Dict × Closure.Dict :=
          match B0.manifest? with
          | some clo =>
            let val := clo.inst 𝕋 self0
            let tm := val.quote 𝕋
            ⟨manifest0 ++ [⟨ℓ, ⟨Γ.values, tm⟩⟩], primary0⟩
          | none =>
            ⟨manifest0, primary0 ++ [⟨ℓ, Closure.const M0_call⟩]⟩

        match ← coeMethod Γ ⟨M0_call, B0self0, B1self1⟩ with
        | .identity _ =>
          let (⟨manifest1', self1'⟩ : Closure.Dict × Closure.Dict) ←
            match B1.manifest? with
            | some clo =>
              let 𝕋 ← get
              let val := clo.inst 𝕋 self1
              let tm := val.quote 𝕋
              pure ⟨manifest1 ++ [⟨ℓ, ⟨Γ.values, tm⟩⟩], primary1⟩
            | none =>
              pure ⟨manifest1, primary1 ++ [⟨ℓ, Closure.const M0_call⟩]⟩
          loop manifest0' self0' manifest1' self1' rest0 rest1

        | .expansion tcoe_M0_call => do
          let 𝕋 ← get
          let vcoe_M0_call := tcoe_M0_call.eval 𝕋 Γ.values
          let (⟨manifest1', self1'⟩ : Closure.Dict × Closure.Dict) ←
            match B1.manifest? with
            | some clo => do
              let val := clo.inst 𝕋 self1
              convert Γ vcoe_M0_call val
              pure ⟨manifest1 ++ [⟨ℓ, clo⟩], primary1⟩
            | none =>
              pure ⟨manifest1, primary1 ++ [⟨ℓ, Closure.const vcoe_M0_call⟩]⟩
          let result ← loop manifest0' self0' manifest1' self1' rest0 rest1
          return .expansion result.get
    | _, _ => throw s!"Sum.coercion: mismatched methods in telescopes {reprStr C0.whnf} vs. {reprStr C1.whnf}"
    do
      match ← loop [] [] [] [] spec0 spec1 with
      | .identity _ => do
        let 𝕋 ← get
        return CoercionResult.identity $ Thunk.mk λ _ => M0.quote 𝕋
      | .expansion ⟨manifest, self⟩ =>
        return CoercionResult.expansion $ .obj locale1? selfName1? manifest self

  | _, _ => throw s!"Sum.coercion: expected sum types: {reprStr C0}, {reprStr C1}"
