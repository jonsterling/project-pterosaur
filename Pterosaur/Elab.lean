import Pterosaur.Refiners
import Pterosaur.Preterm
import Std.Data.HashMap

structure Resolver where
  entries : Std.HashMap Name Defined

instance : EmptyCollection Resolver where
  emptyCollection := ⟨{}⟩

def Resolver.ext (x : Name) (h : Defined) (ρ : Resolver) : Resolver :=
  {ρ with entries := ρ.entries.insert x h}

def Resolver.ext? (x? : Option Name) (h : Defined) (ρ : Resolver) : Resolver :=
  match x? with
  | none => ρ
  | some x => ρ.ext x h

mutual
  partial
  def Preterm.checkTerm (ρ : Resolver) : Preterm → TermChecker ElabM n
  | .lam name M =>
    funIntro name $ Tactic.withTopHyp $
    M.checkTerm ∘ ρ.ext name
  | .pi name A B =>
    funFormation name (A.checkTerm ρ) $ Tactic.withTopHyp $
    B.checkTerm ∘ ρ.ext name
  | .sig spec =>
    recordFormation spec.selfName? $ spec.check ρ
  | .object selfName? (dict : Predict) =>
    recordIntro $ dict.checkObjectDict ρ selfName?
  | .TYPE => universeFormation
  | .reveal name scope =>
    reveal name $ scope.checkTerm ρ
  | .hole name => checkHole name
  | M => ValueSynthesiser.coerce (M.synth ρ) Tactic.autoCoerceTerm

  partial
  def PrelocaleSpecDecl.check (ρ : Resolver) (selfName? : Option String) (name : Name) : PrelocaleSpecDecl → RecordSpecExtender ElabM n
  | .require A => .require selfName? name (Tactic.withTopHyp $ A.checkTerm ∘ ρ.ext? selfName?) none
  | .splice A => .splice selfName? name (Tactic.withTopHyp $ A.checkTerm ∘ ρ.ext? selfName?)

  partial
  def PrelocaleSpec.check (ρ : Resolver) (spec : PrelocaleSpec) : RecordSpecExtender ElabM n :=
    let rec loop : List (Name × PrelocaleSpecDecl) → RecordSpecExtender ElabM n
    | [] => .identity
    | ⟨name, decl⟩ :: decls =>
      .append (decl.check ρ spec.selfName? name) (loop decls);
    loop spec.decls

  partial
  def Preterm.checkValue (ρ : Resolver): Preterm → ValueChecker ElabM n :=
    evalCheckTerm ∘ Preterm.checkTerm ρ

  partial
  def Predict.checkObjectDict (ρ : Resolver) (selfName? : Option String) (dict : Predict) : ObjectDictChecker ElabM n :=
    checkObjectDict selfName? $ dict.map λ ⟨ℓ, M⟩ =>
    ⟨ℓ, Tactic.withTopHyp $ M.checkTerm ∘ ρ.ext? selfName?⟩

  partial
  def Predict.refineRecordSpec (ρ : Resolver) (selfName? : Option String) (dict : Predict) : RecordSpecRefiner ElabM n :=
    .refine selfName? $ dict.map λ ⟨ℓ, M⟩ =>
    ⟨ℓ, Tactic.withTopHyp $ M.checkTerm ∘ ρ.ext? selfName?⟩

  partial
  def Preterm.synth (ρ : Resolver) : Preterm → ValueSynthesiser ElabM n
  | .var name =>
    match ρ.entries[name]? with
    | none => .fail s!"Unresolved name {name}"
    | some hyp => hypothesis hyp
  | .app M N =>
    funElim (M.synth ρ) $ N.checkValue ρ
  | .call M ℓ =>
    recordElim (M.synth ρ) ℓ
  | .refine target selfName? (inst : Predict) =>
    refineRecordType (target.synth ρ) $ inst.refineRecordSpec ρ selfName?
  | .ann term type =>
    ascribe (type.checkValue ρ) (term.checkValue ρ)
  | _ => .fail "Elaboration impossible"
end

def Pretheory.elab (ρ : Resolver) (𝕋 : Pretheory) : ElabM Unit := do
  match 𝕋 with
  | [] => return ()
  | decl :: (𝕋 : Pretheory) =>
    match decl with
    | .define name A M =>
      let entry ← Kernel.define name (tacA := A.checkValue ρ) (tacM := M.checkValue ρ)
      𝕋.elab $ ρ.ext name entry
    | .locale name spec =>
      let localeType ← Kernel.declareLocale name spec.selfName? $ spec.check ρ
      𝕋.elab $ ρ.ext name localeType
    | .extendLocale localeName selfName? name type impl =>
      Kernel.extendLocale localeName name selfName?
        (Tactic.withTopHyp $ type.checkTerm ∘ ρ.ext? selfName?)
        (Tactic.withTopHyp $ impl.checkTerm ∘ ρ.ext? selfName?)
      𝕋.elab ρ

def run (m : ElabM α) : IO α := do
  match ← ExceptT.run $ StateT.run m {} with
  | .ok (a, _) => pure a
  | .error err => throw $ IO.userError err
