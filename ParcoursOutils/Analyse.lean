import ParcoursOutils.Donnees
/-!
# Analyse d'une preuve

Pour chaque déclaration à prouver, on parcourt le terme de preuve
(et les déclarations auxiliaires écrites dans le même fichier) pour savoir :
* s'il reste des `sorry` (ou des `axiom` faits maison, ou `native_decide`) ;
* quels théorèmes de la bibliothèque de Lean sont utilisés,
  et s'ils sont autorisés à ce stade du parcours ;
* quels résultats d'autres exercices sont utilisés, et s'ils sont finis.
-/
open Lean

namespace ParcoursOutils

inductive Statut where
  | introuvable
  | enonceModifie
  | inacheve
  | interdit
  | reussi
  deriving Repr, BEq, Inhabited, ToJson, FromJson

structure RapportCible where
  nom : Name
  statut : Statut
  /-- Théorèmes de la bibliothèque utilisés mais pas encore débloqués. -/
  empruntes : Array Name := #[]
  /-- Constantes explicitement interdites dans cet exercice. -/
  interdits : Array Name := #[]
  /-- Axiomes non standards (axiom maison, native_decide…). -/
  axiomes : Array Name := #[]
  /-- Résultats d'autres exercices utilisés mais pas encore prouvés. -/
  depsInachevees : Array Name := #[]
  deriving Inhabited, Repr

structure RapportExo where
  id : String
  cibles : Array RapportCible
  deriving Inhabited, Repr

def RapportExo.reussi (r : RapportExo) : Bool :=
  !r.cibles.isEmpty && r.cibles.all (·.statut == .reussi)

def RapportExo.pur (r : RapportExo) : Bool :=
  r.reussi && r.cibles.all (·.empruntes.isEmpty)

def RapportExo.empruntes (r : RapportExo) : Array Name :=
  r.cibles.foldl (fun acc c => c.empruntes.foldl (fun a n => if a.contains n then a else a.push n) acc) #[]

def RapportExo.depsInachevees (r : RapportExo) : Array Name :=
  r.cibles.foldl (fun acc c => c.depsInachevees.foldl (fun a n => if a.contains n then a else a.push n) acc) #[]

def axiomesStandards : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Filtrage « glob » : `*` remplace n'importe quelle suite de caractères. -/
partial def glob (p s : List Char) : Bool :=
  match p, s with
  | [], [] => true
  | '*' :: p', _ => glob p' s || (match s with | [] => false | _ :: s' => glob p s')
  | c :: p', d :: s' => c == d && glob p' s'
  | _, _ => false

/-- `*` = tout ; un motif contenant `*` est un glob sur le nom complet (`*dvd*`) ;
sinon c'est un préfixe par composantes (`Nat` couvre `Nat.add_comm`). -/
def motifCorrespond (motif : String) (c : Name) : Bool :=
  if motif == "*" then true
  else if motif.contains '*' then glob motif.toList c.toString.toList
  else motif.toName.isPrefixOf c

def Jeton.couvre (j : Jeton) (c : Name) : Bool :=
  j.motifs.any (motifCorrespond · c) && !j.sauf.any (motifCorrespond · c)

/-- Le module dans lequel `c` est déclaré (`none` = le fichier en cours). -/
def moduleDe (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).bind fun i => env.header.moduleNames[i.toNat]?

/-- Une constante « à toi » : déclarée dans un fichier du parcours (ou le fichier en cours). -/
def estPerso (env : Environment) (c : Name) : Bool :=
  match moduleDe env c with
  | none => true
  | some m => m.getRoot == `Exercices || m.getRoot == `Solutions

/-- Mémo : constante perso ↦ « elle (ou une de ses dépendances) contient sorry ». -/
abbrev AnalyseM := StateM (NameMap Bool)

def exprsDe (ci : ConstantInfo) : Array Expr :=
  match ci.value? (allowOpaque := true) with
  | some v => #[ci.type, v]
  | none => #[ci.type]

/-- Une constante perso est inachevée si elle utilise (transitivement) `sorry`
ou un axiome non standard. -/
partial def estInachevee (env : Environment) (c : Name) : AnalyseM Bool := do
  if let some b := (← get).find? c then return b
  modify (·.insert c false) -- protège contre les cycles
  let res ← do
    match env.find? c with
    | none => pure false
    | some ci =>
      if ci matches .axiomInfo _ then pure true else
      let mut r := false
      for e in exprsDe ci do
        for d in e.getUsedConstants do
          if r then break
          if d == ``sorryAx then r := true
          else if estPerso env d then
            if ← estInachevee env d then r := true
          else if let some (.axiomInfo _) := env.find? d then
            if !axiomesStandards.contains d then r := true
      pure r
  modify (·.insert c res)
  return res

/-- Parcourt la preuve de `cible` et les déclarations auxiliaires du même fichier.
Renvoie (sorry présent ?, axiomes locaux, constantes externes utilisées). -/
def collecter (env : Environment) (cible : Name) : Bool × Array Name × NameSet := Id.run do
  let modC := env.getModuleIdxFor? cible
  let memeModule (c : Name) : Bool :=
    match env.getModuleIdxFor? c, modC with
    | none, none => true
    | some a, some b => a.toNat == b.toNat
    | _, _ => false
  let mut vus : NameSet := {}
  let mut pile : Array Name := #[cible]
  let mut externes : NameSet := {}
  let mut sorryP := false
  let mut axiomesLoc : Array Name := #[]
  while h : pile.size > 0 do
    let n := pile[pile.size - 1]
    pile := pile.pop
    if vus.contains n then continue
    vus := vus.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      if ci matches .axiomInfo _ then axiomesLoc := axiomesLoc.push n
      for e in exprsDe ci do
        for c in e.getUsedConstants do
          if c == ``sorryAx then sorryP := true
          else if memeModule c then
            if !vus.contains c then pile := pile.push c
          else externes := externes.insert c
  return (sorryP, axiomesLoc, externes)

/-- Les jetons effectivement débloqués pour cet exercice
(ceux dont l'exercice « pont » est terminé). -/
def jetonsActifs (env : Environment) (d : DonneesVerif) (exo : ExoVerif) : AnalyseM (Array Jeton) := do
  let mut res := #[]
  for a in exo.autorise do
    let some src := d.exercices.find? (·.id == a.par) | continue
    let mut ok := true
    for c in src.cibles do
      let n := c.toName
      if (env.find? n).isNone then ok := false
      else if ← estInachevee env n then ok := false
    if ok then
      if let some j := d.jetons.find? (·.nom == a.jeton) then res := res.push j
  return res

def analyserCible (env : Environment) (d : DonneesVerif) (exo : ExoVerif)
    (actifs : Array Jeton) (cibleStr : String) : AnalyseM RapportCible := do
  let nom := cibleStr.toName
  let some ci := env.find? nom | return { nom, statut := .introuvable }
  if let some h := exo.hashes.find? (·.cible == cibleStr) then
    if toString ci.type.hash != h.hash then
      return { nom, statut := .enonceModifie }
  let (sorryP, axiomesLoc, externes) := collecter env nom
  let mut empruntes := #[]
  let mut interdits := #[]
  let mut axiomes := axiomesLoc
  let mut deps := #[]
  for c in externes.toList do
    if exo.interdit.any (motifCorrespond · c) then
      interdits := interdits.push c
    else if estPerso env c then
      if ← estInachevee env c then deps := deps.push c
    else match env.find? c with
      | some (.axiomInfo _) =>
        if !axiomesStandards.contains c then axiomes := axiomes.push c
      | some (.thmInfo _) =>
        let autorise := d.base.any (motifCorrespond · c) || exo.permis.any (motifCorrespond · c) ||
          actifs.any (·.couvre c)
        if !autorise then empruntes := empruntes.push c
      | _ => pure ()
  let statut :=
    if sorryP || !axiomes.isEmpty then Statut.inacheve
    else if !interdits.isEmpty then .interdit
    else .reussi
  let tri (a : Array Name) := a.qsort (fun x y => x.toString < y.toString)
  return { nom, statut, empruntes := tri empruntes, interdits := tri interdits,
           axiomes := tri axiomes, depsInachevees := tri deps }

def analyserExo (env : Environment) (d : DonneesVerif) (exo : ExoVerif) : AnalyseM RapportExo := do
  let actifs ← jetonsActifs env d exo
  let cibles ← exo.cibles.mapM (analyserCible env d exo actifs)
  return { id := exo.id, cibles }

/-- Pour une constante perso, l'exercice où elle est déclarée (si on le sait). -/
def exoDeConstante (env : Environment) (d : DonneesVerif) (c : Name) : Option ExoVerif :=
  match moduleDe env c with
  | some m =>
    let comps := m.components.map toString
    match comps with
    | _ :: reste => d.exercices.find? (·.id == ".".intercalate reste)
    | [] => none
  | none => none

/-- Quels exercices débloquent un lemme donné ? -/
def quiDebloque (d : DonneesVerif) (c : Name) : Array String := Id.run do
  let mut res := #[]
  for j in d.jetons do
    if j.couvre c then
      for e in d.exercices do
        if e.debloque.contains j.nom then res := res.push s!"« {e.titre} » ({e.id})"
  return res

def nomCourt (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => toString n

/-- Message lisible (en français) décrivant le résultat d'un exercice. -/
def RapportExo.message (r : RapportExo) (env : Environment) (d : DonneesVerif) (titre : String) : String := Id.run do
  let mut lignes : Array String := #[]
  if r.reussi then
    if r.pur then
      lignes := lignes.push s!"⭐ « {titre} » : réussi, et preuve PURE (uniquement tes propres résultats). Bravo !"
    else
      lignes := lignes.push s!"✅ « {titre} » : réussi !"
      lignes := lignes.push "   Mais pas encore ⭐ : tu as utilisé des théorèmes de la bibliothèque de Lean pas encore débloqués :"
      for c in r.empruntes do
        let qui := quiDebloque d c
        let suffixe := if qui.isEmpty then "" else s!"  (débloqué par {qui[0]!})"
        lignes := lignes.push s!"     • {c}{suffixe}"
      lignes := lignes.push "   C'est permis, mais pour l'étoile, refais ces étapes avec tes propres lemmes."
    let deps := r.depsInachevees
    if !deps.isEmpty then
      lignes := lignes.push "   ⚠️ Ta preuve s'appuie sur des résultats que tu n'as pas encore prouvés :"
      for c in deps do
        let ou := match exoDeConstante env d c with
          | some e => s!" (exercice « {e.titre} »)"
          | none => ""
        lignes := lignes.push s!"     • {c}{ou}"
  else
    lignes := lignes.push s!"❌ « {titre} » : pas encore réussi."
    for c in r.cibles do
      match c.statut with
      | .reussi => lignes := lignes.push s!"   ✔ {nomCourt c.nom} : prouvé."
      | .introuvable => lignes := lignes.push s!"   ✘ {nomCourt c.nom} : introuvable ! (renommé ou supprimé ?)"
      | .enonceModifie => lignes := lignes.push s!"   ✘ {nomCourt c.nom} : l'ÉNONCÉ a été modifié. Remets-le comme à l'origine (`./parcours reset` si besoin)."
      | .inacheve =>
        if c.axiomes.isEmpty then
          lignes := lignes.push s!"   … {nomCourt c.nom} : il reste des `sorry` (ou une erreur)."
        else
          lignes := lignes.push s!"   ✘ {nomCourt c.nom} : utilise des axiomes non autorisés : {c.axiomes.toList} (pas de `axiom` maison ni de `native_decide` !)"
      | .interdit =>
        lignes := lignes.push s!"   ✘ {nomCourt c.nom} : cet exercice interdit d'utiliser : {c.interdits.toList}"
  return "\n".intercalate lignes.toList

end ParcoursOutils
