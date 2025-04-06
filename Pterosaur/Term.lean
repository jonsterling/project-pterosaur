import Pterosaur.Bwd
import Pterosaur.Name
import Lean

mutual
  inductive Term : Nat → Type where
  | localVar (ix : Ix n) : Term n
  | globalVar (name : Name) : Term n
  | funTp {n} (boundName? : Option String) (dom : Term n) (cod : Term (n+1)) : Term n
  | lam (boundName? : Option String) (dom : Term n) (body : Term (n+1)) : Term n
  | rcdTp (locale? : Option Name) (selfName? : Option String) (methods : Term.ManifestDict (n+1)) : Term n
  | obj (locale? : Option Name) (selfName? : Option String) (manifest dict : Term.Dict (n+1)) : Term n
  | app : Term n → Term n → Term n
  | call : Term n → Name → Term n
  | refine : Term n → Option String → Term.ManifestDict (n+1) → Term.Dict (n+1) → Term n
  | error (msg : String) : Term n
  | TYPE : Term n
  deriving Nonempty, Repr

  inductive Term.ManifestDict : Nat → Type where
  | nil : Term.ManifestDict n
  | consAbstract (name : Name) (type : Term n) (rest : Term.ManifestDict n) : Term.ManifestDict n
  | consManifest (name : Name) (type : Term n) (manifest : Term n) (rest : Term.ManifestDict n) : Term.ManifestDict n
  deriving Nonempty, Repr

  inductive Term.Dict : Nat → Type where
  | nil : Term.Dict n
  | cons (name : Name) (term : Term n) (rest : Term.Dict n) : Term.Dict n
  deriving Nonempty, Repr
end

def Term.ManifestDict.lookup (name : Name) : Term.ManifestDict n → Option (Term n × Option (Term n))
| .nil => none
| .consAbstract name' term rest =>
  if name == name' then some ⟨term, none⟩
  else lookup name rest
| .consManifest name' term manifest rest =>
  if name == name' then some ⟨term, manifest⟩
  else lookup name rest

def Term.ManifestDict.ofList : List (Name × (Term n × Option (Term n))) → Term.ManifestDict n
| [] => .nil
| ⟨name, term, none⟩ :: rest => .consAbstract name term $ ofList rest
| ⟨name, term, some manifest⟩ :: rest => .consManifest name term manifest $ ofList rest

def Term.ManifestDict.toList : Term.ManifestDict n → List (Name × (Term n × Option (Term n)))
| .nil => []
| .consAbstract name term rest => ⟨name, term, none⟩ :: rest.toList
| .consManifest name term manifest rest => ⟨name, term, some manifest⟩ :: rest.toList

def Term.Dict.lookup (name : Name) : Term.Dict n → Option (Term n)
| .nil => none
| .cons name' term rest =>
  if name == name' then some term
  else lookup name rest

def Term.Dict.ofList : List (Name × Term n) → Term.Dict n
| [] => .nil
| ⟨name, term⟩ :: rest => .cons name term $ Term.Dict.ofList rest

def Term.Dict.toList : Term.Dict n → List (Name × Term n)
| .nil => []
| .cons name term rest => ⟨name, term⟩ :: rest.toList

open Lean.Parser (maxPrec argPrec minPrec)

mutual
  partial
  def Term.format (ρ : Bwd String n) (prec : Nat) : Term n → Std.Format
  | .localVar ix => Option.getD (ρ.proj ix) (repr ix)
  | .globalVar name => repr name
  | .app e1 e2 => fmtApp <| e1.format ρ argPrec ++ .line ++ e2.format ρ maxPrec
  | .call e ℓ => e.format ρ maxPrec ++ "·" ++ repr ℓ
  | .lam name? _dom body =>
    let name := Option.getD name? "_"
    .group $ "λ " ++ name ++ " => " ++ .nest 2 (body.format (ρ⬝name) minPrec)
  | .funTp name? dom fam =>
    let name := Option.getD name? "_"
    .group $ "(" ++ name ++ " : " ++ dom.format ρ minPrec ++ ")" ++ " →" ++ .line ++ fam.format (ρ⬝name) minPrec

  | .rcdTp none selfName? methods =>
    let selfName := Option.getD selfName? "_"
    let body :=
      (f!"," ++ .line).joinSep $ methods.toList.map λ ⟨ℓ, type, manifest?⟩ =>
      repr ℓ ++
      match manifest? with
      | none => " : " ++ type.format (ρ⬝selfName) minPrec
      | some manifest => " := " ++ manifest.format (ρ ⬝ selfName) minPrec
    let binder :=
      match selfName? with
      | none => .nil
      | some selfName => f!"{selfName} => "
    .group $ "record " ++ "{" ++ binder  ++ .nest 1 body ++ "}"

  | .rcdTp (some localeName) selfName? methods =>
    let selfName := Option.getD selfName? "_"
    let manifestMethods : List Std.Format :=
      methods.toList.filterMap λ ⟨ℓ, _, manifest?⟩ =>
      manifest?.map λ manifest =>
      repr ℓ ++ " := " ++ manifest.format (ρ ⬝ selfName) minPrec
    match manifestMethods with
    | [] => Repr.addAppParen (.group $ "instance " ++ repr localeName) prec
    | _ =>
      let body := (f!"," ++ .line).joinSep manifestMethods
      let binder :=
        match selfName? with
        | none => .nil
        | some selfName => f!"{selfName} => "

      Repr.addAppParen (.group $ "instance " ++ repr localeName ++ " {" ++ binder ++ .nest 1 body ++ "}") prec

  | .obj _ selfName? _ methods =>
    let selfName := Option.getD selfName? "_"
    let body :=
      (f!"," ++ .line).joinSep $
      methods.toList.map λ ⟨ℓ, impl⟩ =>
      repr ℓ ++ " := " ++ impl.format (ρ ⬝ selfName) minPrec
    let binder :=
      match selfName? with
      | none => .nil
      | some selfName => f!"{selfName} => "
    Repr.addAppParen (.group $ "{" ++ binder ++ .nest 1 body ++ "}") prec

  | .refine target selfName? _ methods =>
    let selfName := Option.getD selfName? "_"
    let manifestMethods : List Std.Format :=
      methods.toList.filterMap λ ⟨ℓ, term⟩ =>
      repr ℓ ++ " := " ++ term.format (ρ ⬝ selfName) minPrec
    let body := (f!"," ++ .line).joinSep manifestMethods
    let binder :=
      match selfName? with
      | none => .nil
      | some selfName => f!"{selfName} => "
    Repr.addAppParen (.group $ target.format ρ minPrec ++ " / " ++ "{" ++ binder ++ .nest 1 body ++ "}") prec

  | .TYPE => "Type"
  | .error msg => f!"!ERROR![{msg}]"
  where
    fmtApp (elts : Std.Format) : Std.Format :=
      Repr.addAppParen (.group (.nest 2 elts)) prec

  partial
  def Term.Dict.format (ρ : Bwd String n) : Term.Dict n → Std.Format
  | .nil => .nil
  | .cons _ (.obj _ _ _ .nil) dict => dict.format ρ
  | .cons name term .nil => repr name ++ " := " ++ .nest 1 (term.format ρ minPrec)
  | .cons name term dict => repr name ++ " := " ++ .nest 1 (term.format ρ minPrec ++ ",") ++ .line ++ dict.format ρ
end


def buildLocalVarSpineGen : (n : Nat) → (f : Ix n → Ix m) → Bwd (Ix m) n
| 0, _ => {}
| n+1, f => buildLocalVarSpineGen n (f ∘ .pop) ⬝ f .top

def buildLocalVarSpine (n : Nat) : Bwd (Ix n) n :=
  buildLocalVarSpineGen n id

def plugLocalVarSpine (M : Term n) : {m : Nat} → Bwd (Ix n) m → Term n
| 0, .emp => M
| _+1, .snoc ixs ix => .app (plugLocalVarSpine M ixs) (.localVar ix)
