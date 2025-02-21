import Pterosaur.Preterm
import Pterosaur.Prelude
import Pterosaur.Theory
import Pterosaur.Name
import Pterosaur.Elab

import Lean
open Lean hiding Name

declare_syntax_cat tt.term
declare_syntax_cat tt.decl
declare_syntax_cat tt.thy
declare_syntax_cat tt.localeSpec
declare_syntax_cat tt.localeSpecDecl
declare_syntax_cat tt.objDecl
declare_syntax_cat tt.prodTeleCell

syntax "(" ident+ ":" tt.term ")" : tt.prodTeleCell

syntax "⟦" tt.term "⟧" : term
syntax:max "?" optional(ident) : tt.term
syntax:max ident : tt.term
syntax tt.term ":" tt.term : tt.term
syntax:max "λ" ident+ "=>" tt.term:arg : tt.term
syntax:max tt.prodTeleCell+ "→" tt.term : tt.term

syntax "record" "{" tt.localeSpec "}" : tt.term

syntax tt.term "/" "{" ident "=>" tt.objDecl,+ "}" : tt.term
syntax tt.term "/" "{" tt.objDecl,+ "}" : tt.term

syntax "{" tt.objDecl,* "}" : tt.term
syntax "{" ident "=>" tt.objDecl,* "}" : tt.term

syntax "(" tt.term ")" : tt.term

syntax "reveal" ident* "in" tt.term : tt.term

syntax ident "=>" tt.localeSpecDecl,* : tt.localeSpec
syntax tt.localeSpecDecl,* : tt.localeSpec

syntax:arg tt.term:arg tt.term:max : tt.term
syntax:max tt.term:arg "·" ident : tt.term

syntax "Type" : tt.term

syntax "decl⟦" tt.decl "⟧" : term
syntax "localeSpecDecl⟦" tt.localeSpecDecl "⟧" : term
syntax "objDecl⟦" tt.objDecl "⟧" : term
syntax "localeSpec⟦" tt.localeSpec "⟧" : term
syntax "thy⟦" tt.thy "⟧" : term
syntax "thy!⟦" tt.thy "⟧" : term
syntax "prodTeleCell⟦" tt.prodTeleCell "⟧" : term
syntax "buildLambdas⟦" tt.prodTeleCell* "=>" tt.term "⟧" : term


syntax withPosition("def" ident tt.prodTeleCell* ":" tt.term ":=" colGt tt.term) : tt.decl
syntax withPosition("for" ident ":" ident colGt "def" ident ":" tt.term ":=" colGt tt.term) : tt.decl

syntax withPosition("locale" ident "{" tt.localeSpec "}") : tt.decl

syntax tt.decl* : tt.thy

syntax ident ":" tt.term : tt.localeSpecDecl
syntax "splice" ident ":" tt.term : tt.localeSpecDecl
syntax ident+ ":=" tt.term : tt.objDecl


macro_rules
| `(prodTeleCell⟦($x : $A)⟧) =>
  let xstr : StrLit := quote (toString x.getId)
  `(Preterm.pi $xstr ⟦$A⟧)
| `(prodTeleCell⟦($x $y $ys* : $A)⟧) =>
  let xstr : StrLit := quote (toString x.getId)
  `(Preterm.pi $xstr ⟦$A⟧ ∘ prodTeleCell⟦($y $ys* : $A)⟧)

macro_rules
| `(⟦$x:ident⟧) =>
  let xstr : StrLit := quote (toString x.getId)
  `(Preterm.var $xstr)
| `(⟦Type⟧) => `(Preterm.TYPE)
| `(⟦λ $x => $body⟧) =>
  let xstr : StrLit := quote (toString x.getId)
  `(Preterm.lam $xstr ⟦$body⟧)
| `(⟦λ $x $y $xs* => $body⟧) =>
  let xstr : StrLit := quote (toString x.getId)
  `(Preterm.lam $xstr ⟦λ $y $xs* => $body⟧)

| `(⟦?⟧) =>
  `(Preterm.hole "_")

| `(⟦?$x⟧) =>
  let xstr : StrLit := quote (toString x.getId)
  `(Preterm.hole $xstr)

| `(⟦$cell:tt.prodTeleCell → $B⟧) =>
  `(prodTeleCell⟦ $cell ⟧ ⟦$B⟧)

| `(⟦$cell:tt.prodTeleCell $cell':tt.prodTeleCell $cells:tt.prodTeleCell* → $B⟧) =>
  `(prodTeleCell⟦ $cell ⟧ ⟦$cell':tt.prodTeleCell $cells:tt.prodTeleCell* → $B⟧)

| `(⟦record {$obj}⟧) =>
  `(Preterm.sig localeSpec⟦$obj⟧)

| `(⟦$A / {$[$d],*}⟧) =>
  `(Preterm.refine ⟦$A⟧ none [ $[objDecl⟦$d⟧],* ] )

| `(⟦$A / {$self => $[$d],*}⟧) =>
  let selfstr : StrLit := quote (toString self.getId);
  `(Preterm.refine ⟦$A⟧ $selfstr [ $[objDecl⟦$d⟧],* ] )

| `(⟦{$[$d],*}⟧) =>
  `(Preterm.object none [ $[objDecl⟦$d⟧],* ])

| `(⟦{$self => $[$d],*}⟧) =>
  let selfstr : StrLit := quote (toString self.getId);
  `(Preterm.object $selfstr [ $[objDecl⟦$d⟧],* ])

| `(⟦$e·$ℓ⟧) =>
  let str : StrLit := quote (toString ℓ.getId)
  `(Preterm.call ⟦$e⟧ $str)

| `(⟦$f $u⟧) =>
  `(Preterm.app ⟦$f⟧ ⟦$u⟧)

| `(⟦($e:tt.term)⟧ ) => `(⟦$e⟧)

| `(⟦reveal in $M⟧) =>
  `(⟦$M⟧)

| `(⟦reveal $x $xs* in $M⟧) =>
  let xstr : StrLit := quote (toString x.getId)
  `(Preterm.reveal $xstr ⟦reveal $xs* in $M⟧)

macro_rules
| `(buildLambdas⟦=> $M⟧) => `(⟦$M⟧)
| `(buildLambdas⟦($x : $A) $cells:tt.prodTeleCell* => $M:tt.term⟧) =>
  let xstr : StrLit := quote (toString x.getId)
  `(Preterm.lam $xstr buildLambdas⟦$cells:tt.prodTeleCell* => $M:tt.term⟧)
| `(buildLambdas⟦($x $y $ys* : $A) $cells* => $M⟧) =>
  let xstr : StrLit := quote (toString x.getId)
  `(Preterm.lam $xstr buildLambdas⟦($y $ys* : $A) $cells:tt.prodTeleCell* => $M:tt.term⟧)


macro_rules
| `(decl⟦def $x : $A := $M⟧) =>
  let xstr : StrLit := quote (toString x.getId)
  `(Predecl.define $xstr ⟦$A⟧ ⟦$M⟧)

| `(decl⟦def $x $cell $cells* : $A := $M⟧) =>
  let xstr : StrLit := quote (toString x.getId)
  `(Predecl.define $xstr ⟦$cell:tt.prodTeleCell $cells:tt.prodTeleCell* → $A⟧ buildLambdas⟦$cell $cells* => $M⟧)


| `(decl⟦for $self : $loc def $x : $A := $M⟧) =>
  let locstr : StrLit := quote (toString loc.getId)
  let xstr : StrLit := quote (toString x.getId)
  let selfstr : StrLit := quote (toString self.getId)
  `(Predecl.extendLocale $locstr $selfstr $xstr ⟦$A⟧ ⟦$M⟧)

| `(decl⟦locale $x {$tele}⟧) =>
  let xstr : StrLit := quote (toString x.getId)
  `(Predecl.locale $xstr localeSpec⟦$tele⟧)

macro_rules
| `(localeSpecDecl⟦$x:ident : $A⟧) =>
  let xstr : StrLit := quote (toString x.getId)
  `(⟨$xstr, .require ⟦$A⟧⟩)
| `(localeSpecDecl⟦splice $x:ident : $A⟧) =>
  let xstr : StrLit := quote (toString x.getId)
  `(⟨$xstr, .splice ⟦$A⟧⟩)
| `(objDecl⟦$x:ident := $A⟧) =>
  let xstr : StrLit := quote (toString x.getId)
  `(⟨$xstr, ⟦$A⟧⟩)
| `(objDecl⟦$x:ident $y:ident $ys:ident* := $A⟧) =>
  let xstr : StrLit := quote (toString x.getId)
  `(⟨$xstr, ⟦λ $y $ys* => $A⟧⟩)


macro_rules
| `(localeSpec⟦$[$d],*⟧) => `(PrelocaleSpec.mk none [ $[localeSpecDecl⟦$d⟧],* ])
| `(localeSpec⟦$x:ident => $[$d],*⟧) =>
  let xstr : StrLit := quote (toString x.getId)
  `(PrelocaleSpec.mk $xstr [ $[localeSpecDecl⟦$d⟧],* ])


macro_rules
| `(thy⟦$[$d]*⟧) => `([ $[decl⟦$d⟧],* ])

macro_rules
| `(thy!⟦$th⟧) => `(run $ do Pretheory.elab {} thy⟦$th⟧)
