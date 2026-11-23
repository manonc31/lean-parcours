import ParcoursOutils.Analyse
import Lean
/-!
# `./parcours` — la ligne de commande du parcours

    ./parcours                 ce que tu peux faire maintenant
    ./parcours verifier        recompile tout, met à jour l'arbre et la carte
    ./parcours arbre [branche] l'arbre complet
    ./parcours info <exo>      l'énoncé d'un exercice
    ./parcours indice <exo>    révèle l'indice suivant
    ./parcours solution <exo>  affiche la solution (avec confirmation)
    ./parcours ouvrir <exo>    ouvre l'exercice dans VS Code
    ./parcours carte           ouvre la carte interactive (progression.html)
    ./parcours reset <exo>     remet un exercice à zéro
-/
open Lean ParcoursOutils

namespace ParcoursCli

/-! ## Données du graphe -/

structure Branche where
  id : String
  titre : String
  emoji : String
  description : String
  deriving FromJson, ToJson, Inhabited

structure ExoInfo where
  id : String
  titre : String
  branche : String
  difficulte : Nat
  genre : String
  fichier : String
  solution : String
  deps : Array String
  importe : Array String
  debloque : Array String
  enonce : String
  indices : Array String
  /-- Numéro dans la liste des « 100 théorèmes » de Freek Wiedijk (0 = aucun). -/
  celebre : Nat
  deriving FromJson, ToJson, Inhabited

structure Graphe where
  branches : Array Branche
  exercices : Array ExoInfo
  deriving FromJson, ToJson, Inhabited

/-- État d'un exercice après vérification. -/
structure EtatExo where
  statut : String  -- pur | reussi | inacheve | erreur | bloque | modifie | interdit | cours
  empruntes : Array String := #[]
  depsInachevees : Array String := #[]
  message : String := ""
  deriving FromJson, ToJson, Inhabited

structure Etat where
  exos : Array (String × EtatExo)
  deriving FromJson, ToJson, Inhabited

def Etat.get (e : Etat) (id : String) : Option EtatExo :=
  (e.exos.find? (·.1 == id)).map (·.2)

/-! ## Couleurs -/

def gras (s : String) := s!"\x1b[1m{s}\x1b[0m"
def vert (s : String) := s!"\x1b[32m{s}\x1b[0m"
def jaune (s : String) := s!"\x1b[33m{s}\x1b[0m"
def rouge (s : String) := s!"\x1b[31m{s}\x1b[0m"
def gris (s : String) := s!"\x1b[90m{s}\x1b[0m"
def cyan (s : String) := s!"\x1b[36m{s}\x1b[0m"

/-! ## Utilitaires -/

def lireJson (α) [FromJson α] (p : System.FilePath) : IO α := do
  let txt ← IO.FS.readFile p
  match Json.parse txt >>= fromJson? with
  | .ok v => return v
  | .error e => throw <| IO.userError s!"{p} illisible : {e}"

def ecrireJson {α} [ToJson α] (p : System.FilePath) (v : α) : IO Unit := do
  if let some d := p.parent then IO.FS.createDirAll d
  IO.FS.writeFile p (toJson v).pretty

def etoiles (n : Nat) : String :=
  String.join ((List.range 5).map fun i => if i < n then "★" else "☆")

def ExoInfo.decor (e : ExoInfo) : String :=
  match e.genre with
  | "boss" => "💀 "
  | "ouvert" => "♾️  "
  | "pont" => "🌉 "
  | "cours" => "📖 "
  | _ => ""

def estFini (s : String) : Bool := s == "pur" || s == "reussi" || s == "cours"

structure Ctx where
  racine : System.FilePath
  graphe : Graphe
  etat : Etat

def Ctx.statut (c : Ctx) (e : ExoInfo) : String :=
  if e.genre == "cours" then "cours" else
  match c.etat.get e.id with
  | some s => s.statut
  | none => "inconnu"

/-- Un exercice est acquis s'il est réussi ; un cours, si ses prérequis sont acquis. -/
partial def Ctx.fini (c : Ctx) (id : String) : Bool :=
  match c.graphe.exercices.find? (·.id == id) with
  | some e => if e.genre == "cours" then e.deps.all c.fini else estFini (c.statut e)
  | none => true

def Ctx.disponible (c : Ctx) (e : ExoInfo) : Bool :=
  !c.fini e.id && e.deps.all c.fini

def Ctx.icone (c : Ctx) (e : ExoInfo) : String :=
  match c.statut e with
  | "pur" => "⭐"
  | "reussi" => "✅"
  | "cours" => if c.fini e.id then "📖" else "🔒"
  | "erreur" => "❗"
  | "modifie" => "⚠️ "
  | "interdit" => "🚫"
  | _ => if c.disponible e then "🎯" else "🔒"

/-- Profondeur dans le graphe (plus long chemin depuis une racine). -/
partial def profondeurs (g : Graphe) : Std.HashMap String Nat := Id.run do
  let mut memo : Std.HashMap String Nat := {}
  let rec prof (fuel : Nat) (memo : Std.HashMap String Nat) (id : String) : Nat × Std.HashMap String Nat :=
    match memo.get? id with
    | some p => (p, memo)
    | none =>
      match fuel, g.exercices.find? (·.id == id) with
      | 0, _ | _, none => (0, memo)
      | fuel + 1, some e => Id.run do
        let mut m := memo
        let mut best := 0
        for d in e.deps do
          let (p, m') := prof fuel m d
          m := m'
          best := max best (p + 1)
        return (best, m.insert id best)
  for e in g.exercices do
    memo := (prof 500 memo e.id).2
  return memo

def ordreBranche (g : Graphe) (b : String) : Nat :=
  (g.branches.findIdx? (·.id == b)).getD 1000

def trierExos (g : Graphe) (es : Array ExoInfo) : Array ExoInfo :=
  let p := profondeurs g
  es.qsort fun a b =>
    let ka := (ordreBranche g a.branche, p.getD a.id 0)
    let kb := (ordreBranche g b.branche, p.getD b.id 0)
    ka.1 < kb.1 || (ka.1 == kb.1 && (ka.2 < kb.2 || (ka.2 == kb.2 && a.id < b.id)))

def normaliser (s : String) : String :=
  String.ofList (s.toList.filter (fun c => c.isAlphanum)) |>.toLower

/-- Trouve un exercice à partir d'un nom approximatif. -/
def trouverExo (g : Graphe) (q : String) : Except String ExoInfo := do
  if let some e := g.exercices.find? (·.id == q) then return e
  -- un chemin de fichier : « Exercices/Naturels/AddComm.lean »
  if let some e := g.exercices.find? (fun e => q.endsWith e.fichier || e.fichier.endsWith q) then
    if q.endsWith ".lean" then return e
  let nq := normaliser q
  let exacts := g.exercices.filter fun e =>
    normaliser e.id == nq || normaliser ((e.id.splitOn ".").getLast!) == nq
  if h : exacts.size = 1 then return exacts[0]
  let partiels := g.exercices.filter fun e =>
    (normaliser e.id).contains nq || (normaliser e.titre).contains nq
  let cands := if exacts.size > 1 then exacts else partiels
  if h : cands.size = 1 then return cands[0]
  if cands.isEmpty then throw s!"Aucun exercice ne correspond à « {q} »."
  let liste := cands.toList.take 15 |>.map (fun e => s!"  • {e.id}  ({e.titre})")
  throw s!"Plusieurs exercices correspondent à « {q} » :\n{"\n".intercalate liste}"

def chargerCtx : IO Ctx := do
  let cwd ← IO.currentDir
  let some racine ← trouverRacine cwd
    | throw <| IO.userError "Lance cette commande depuis le dossier du parcours."
  let graphe ← lireJson Graphe (racine / ".parcours" / "graphe.json")
  let etatF := racine / ".parcours" / "etat.json"
  let etat ← if ← etatF.pathExists then lireJson Etat etatF else pure { exos := #[] }
  return { racine, graphe, etat }

/-! ## Indices révélés -/

structure Reveles where
  exos : Array (String × Nat)
  deriving FromJson, ToJson, Inhabited

def fichierReveles (c : Ctx) := c.racine / ".parcours" / "indices_reveles.json"

def lireReveles (c : Ctx) : IO Reveles := do
  if ← (fichierReveles c).pathExists then lireJson Reveles (fichierReveles c) else pure { exos := #[] }

/-! ## Vérification (compilation + analyse) -/

def modulePour (arbre : String) (id : String) : Name :=
  (arbre ++ "." ++ id).toName

structure ResultatBuild where
  echecs : Array String          -- ids d'exercices dont le fichier ne compile pas
  erreurs : Array (String × String) -- (id, premier message d'erreur)
  sortie : String

def idDeModule (arbre : String) (m : String) : Option String :=
  if m.startsWith (arbre ++ ".") then some (m.drop (arbre.length + 1)).toString else none

def idDeChemin (arbre : String) (p : String) : Option String :=
  -- « Exercices/Naturels/AddComm.lean:12:4: ... »
  let p := (p.splitOn ".lean:").head!
  let comps := p.splitOn "/"
  let comps := comps.dropWhile (· != arbre)
  match comps with
  | _ :: reste@(_ :: _) => some (".".intercalate reste)
  | _ => none

/-- Lance `lake build <arbre>` en affichant la progression sur une ligne. -/
def lancerBuild (racine : System.FilePath) (arbre : String) (silencieux := false) : IO ResultatBuild := do
  let lake := (← IO.getEnv "LAKE").getD "lake"
  let child ← IO.Process.spawn {
    cmd := "/bin/sh", args := #["-c", s!"'{lake}' build {arbre} 2>&1"],
    cwd := racine, stdout := .piped, stderr := .null, stdin := .null }
  let mut echecs : Array String := #[]
  let mut erreurs : Array (String × String) := #[]
  let mut sortie := ""
  let mut enErreur : Option (String × String) := none
  repeat
    let ligne ← child.stdout.getLine
    if ligne.isEmpty then break
    sortie := sortie ++ ligne
    let l := ligne.trimAsciiEnd.toString
    let lt := l.trimAsciiStart.toString
    -- Progression « ✔ [12/80] Built Exercices.X »
    if lt.startsWith "✔ [" || lt.startsWith "⚠ [" || lt.startsWith "✖ [" || lt.startsWith "ℹ [" then
      if let some e := enErreur then erreurs := erreurs.push e; enErreur := none
      if !silencieux then
        let court := if l.length > 70 then (l.take 70).toString ++ "…" else l
        IO.print s!"\r\x1b[2K{gris court}"
        (← IO.getStdout).flush
      if lt.startsWith "✖" then
        let mot := (lt.splitOn " ").getLast!
        if let some id := idDeModule arbre mot then
          if !echecs.contains id then echecs := echecs.push id
    else if lt.startsWith "error:" then
      if let some e := enErreur then erreurs := erreurs.push e
      let reste := (lt.drop 6).toString.trimAsciiStart.toString
      match idDeChemin arbre reste with
      | some id =>
        if !echecs.contains id then echecs := echecs.push id
        enErreur := some (id, reste)
      | none => enErreur := none
    else if lt.startsWith "warning:" || lt.startsWith "info:" || lt.startsWith "trace:" then
      if let some e := enErreur then erreurs := erreurs.push e; enErreur := none
    else if let some (id, m) := enErreur then
      if m.length < 1500 then enErreur := some (id, m ++ "\n" ++ l)
  if let some e := enErreur then erreurs := erreurs.push e
  let _ ← child.wait
  if !silencieux then IO.print "\r\x1b[2K"
  return { echecs, erreurs, sortie }

/-- Les exercices qui dépendent (transitivement) d'un exercice en échec. -/
def bloques (g : Graphe) (echecs : Array String) : Array String := Id.run do
  let mut res : Array String := #[]
  let mut change := true
  while change do
    change := false
    for e in g.exercices do
      if !res.contains e.id && !echecs.contains e.id then
        if e.importe.any (fun d => echecs.contains d || res.contains d) then
          res := res.push e.id
          change := true
  return res

def analyserArbre (racine : System.FilePath) (g : Graphe) (arbre : String)
    (echecs bloq : Array String) : IO (Array (String × EtatExo)) := do
  let donnees ← chargerDonnees racine
  let mut mods : Array Import := #[]
  let mut aAnalyser : Array ExoInfo := #[]
  for e in g.exercices do
    if echecs.contains e.id || bloq.contains e.id then continue
    let olean := racine / ".lake" / "build" / "lib" / "lean" / arbre /
      (System.FilePath.mk ("/".intercalate (e.id.splitOn ".")) |>.addExtension "olean")
    if ← olean.pathExists then
      mods := mods.push { module := modulePour arbre e.id }
      aAnalyser := aAnalyser.push e
  initSearchPath (← findSysroot)
  let env ← importModules mods {} (loadExts := false)
  let mut memo : NameMap Bool := {}
  let mut res := #[]
  for e in g.exercices do
    if e.genre == "cours" then
      res := res.push (e.id, { statut := "cours" })
    else if echecs.contains e.id then
      res := res.push (e.id, { statut := "erreur" })
    else if bloq.contains e.id then
      res := res.push (e.id, { statut := "bloque" })
    else if !aAnalyser.any (·.id == e.id) then
      res := res.push (e.id, { statut := "inacheve" })
    else
      let some ev := donnees.exercices.find? (·.id == e.id)
        | res := res.push (e.id, { statut := "inacheve" })
      let (r, m') := (analyserExo env donnees ev).run memo
      memo := m'
      let statut :=
        if r.cibles.any (·.statut == .enonceModifie) then "modifie"
        else if r.cibles.any (·.statut == .introuvable) then "modifie"
        else if r.cibles.any (·.statut == .interdit) then "interdit"
        else if r.pur then "pur"
        else if r.reussi then "reussi"
        else "inacheve"
      res := res.push (e.id, {
        statut,
        empruntes := r.empruntes.map toString,
        depsInachevees := r.depsInachevees.map toString,
        message := r.message env donnees e.titre })
  return res

/-! ## Carte HTML -/

def echapperUrl (s : String) : String :=
  s.replace " " "%20"

def genererCarte (c : Ctx) : IO System.FilePath := do
  let modele ← IO.FS.readFile (c.racine / "Outils" / "carte_modele.html")
  let reveles ← lireReveles c
  let exos ← c.graphe.exercices.mapM fun e => do
    let solFichier := c.racine / e.solution
    let sol ← if e.solution != "" && (← solFichier.pathExists) then IO.FS.readFile solFichier else pure ""
    let etat := c.etat.get e.id |>.getD { statut := if e.genre == "cours" then "cours" else "inconnu" }
    let nbReveles := (reveles.exos.find? (·.1 == e.id)).map (·.2) |>.getD 0
    return Json.mkObj [
      ("id", e.id), ("titre", e.titre), ("branche", e.branche),
      ("difficulte", e.difficulte), ("genre", e.genre),
      ("fichier", e.fichier),
      ("lien", "vscode://file" ++ echapperUrl (c.racine / e.fichier).toString),
      ("deps", toJson e.deps), ("debloque", toJson e.debloque),
      ("enonce", e.enonce), ("indices", toJson e.indices),
      ("reveles", nbReveles),
      ("celebre", e.celebre),
      ("solution", sol),
      ("statut", etat.statut), ("disponible", c.disponible e),
      ("empruntes", toJson etat.empruntes), ("message", etat.message)]
  let donnees := Json.mkObj [
    ("branches", toJson c.graphe.branches),
    ("exercices", Json.arr exos),
    ("racine", c.racine.toString)]
  let html := modele.replace "/*__DONNEES__*/null" donnees.compress
  let sortie := c.racine / "progression.html"
  IO.FS.writeFile sortie html
  return sortie

/-! ## Affichage -/

def ligneExo (c : Ctx) (e : ExoInfo) (avecBranche := false) : String :=
  let br := if avecBranche then
    match c.graphe.branches.find? (·.id == e.branche) with
    | some b => gris s!"[{b.titre}] "
    | none => ""
    else ""
  let titre := e.decor ++ e.titre
  let titre := if c.fini e.id then vert titre
    else if c.disponible e then gras titre else gris titre
  s!"  {c.icone e} {jaune (etoiles e.difficulte)} {br}{titre}  {gris e.id}"

def resume (c : Ctx) : String :=
  let exos := c.graphe.exercices.filter (·.genre != "cours")
  let faits := exos.filter (fun e => estFini (c.statut e))
  let purs := exos.filter (fun e => c.statut e == "pur")
  s!"{gras "Parcours Lean"} — {vert s!"{faits.size}"}/{exos.size} exercices réussis · {jaune s!"{purs.size} ⭐"}"

def afficherDisponibles (c : Ctx) (max : Nat := 25) : IO Unit := do
  let dispo := trierExos c.graphe (c.graphe.exercices.filter fun e => e.genre != "cours" && c.disponible e)
  if dispo.isEmpty then
    IO.println "  (rien de disponible : lance `./parcours verifier`)"
  IO.println (gras s!"Tu peux faire maintenant ({dispo.size}) :")
  for e in dispo.toList.take max do
    IO.println (ligneExo c e (avecBranche := true))
    IO.println (gris s!"        → {e.fichier}")
  if dispo.size > max then
    IO.println (gris s!"  … et {dispo.size - max} autres (`./parcours arbre`)")

def afficherErreurs (c : Ctx) : IO Unit := do
  let errs := c.graphe.exercices.filter fun e => c.statut e == "erreur"
  if !errs.isEmpty then
    IO.println (rouge (gras s!"❗ {errs.size} fichier(s) ne compilent pas :"))
    for e in errs do
      IO.println (rouge s!"  • {e.fichier}")
    IO.println (gris "  Les exercices qui en dépendent ne peuvent pas être vérifiés. Corrige l'erreur,")
    IO.println (gris "  ou remets temporairement `sorry` à la place de la preuve cassée.")
  let modifs := c.graphe.exercices.filter fun e => c.statut e == "modifie"
  for e in modifs do
    IO.println (jaune s!"⚠️  {e.fichier} : énoncé modifié ou théorème renommé (`./parcours reset {e.id}` pour repartir de zéro).")

def aide : String := "
Commandes :
  ./parcours                 ce que tu peux faire maintenant
  ./parcours verifier        recompile, vérifie tout, met à jour la carte
  ./parcours arbre [branche] l'arbre complet (toutes les branches ou une seule)
  ./parcours branches        la liste des branches et ta progression
  ./parcours info <exo>      l'énoncé et les dépendances d'un exercice
  ./parcours indice <exo>    révèle l'indice suivant (un à la fois)
  ./parcours solution <exo>  affiche la solution (demande confirmation)
  ./parcours ouvrir <exo>    ouvre l'exercice dans VS Code
  ./parcours carte           ouvre la carte interactive dans le navigateur
  ./parcours reset <exo>     remet un exercice dans son état d'origine
  ./parcours aide            cette aide

<exo> peut être approximatif : « addcomm », « Naturels.AddComm », « commutativ »…
"

def cmdStatut (c : Ctx) : IO Unit := do
  IO.println (resume c)
  if c.etat.exos.isEmpty then
    IO.println (jaune "Aucune vérification encore faite : lance `./parcours verifier` (la première fois prend 1 à 2 minutes).")
  IO.println ""
  afficherErreurs c
  afficherDisponibles c
  IO.println (gris "\n`./parcours aide` pour toutes les commandes · `./parcours carte` pour la carte interactive")

def cmdArbre (c : Ctx) (filtre : Option String) : IO Unit := do
  IO.println (resume c)
  let p := profondeurs c.graphe
  for b in c.graphe.branches do
    if let some f := filtre then
      if normaliser f != normaliser b.id && !(normaliser b.titre).contains (normaliser f) then continue
    let es := trierExos c.graphe (c.graphe.exercices.filter (·.branche == b.id))
    if es.isEmpty then continue
    let vrais := es.filter (·.genre != "cours")
    let faits := vrais.filter fun e => estFini (c.statut e)
    IO.println ""
    IO.println (gras s!"{b.emoji} {b.titre}  {gris s!"({faits.size}/{vrais.size})"}")
    let base := es.foldl (fun m e => min m (p.getD e.id 0)) 1000
    for e in es do
      let indent := String.ofList (List.replicate (min 6 (p.getD e.id 0 - base)) ' ')
      let manque := e.deps.filter (fun d => !c.fini d)
      let req := if manque.isEmpty || c.fini e.id then "" else
        gris s!"  ← requiert {", ".intercalate manque.toList}"
      IO.println s!"{indent}{ligneExo c e}{req}"

def cmdBranches (c : Ctx) : IO Unit := do
  IO.println (resume c)
  IO.println ""
  for b in c.graphe.branches do
    let es := c.graphe.exercices.filter (fun e => e.branche == b.id && e.genre != "cours")
    let faits := es.filter fun e => estFini (c.statut e)
    let dispo := es.filter fun e => c.disponible e
    IO.println s!"{b.emoji} {gras b.titre} {gris s!"({b.id})"} — {faits.size}/{es.size}, {dispo.size} disponible(s)"
    IO.println (gris s!"    {b.description}")

def cmdInfo (c : Ctx) (q : String) : IO Unit := do
  match trouverExo c.graphe q with
  | .error m => IO.println m
  | .ok e =>
    IO.println s!"{c.icone e} {gras (e.decor ++ e.titre)}  {jaune (etoiles e.difficulte)}  {gris e.id}"
    IO.println (cyan s!"Fichier : {e.fichier}")
    if !e.deps.isEmpty then
      IO.println "Dépend de :"
      for d in e.deps do
        if let some de := c.graphe.exercices.find? (·.id == d) then
          IO.println s!"  {c.icone de} {de.titre}  {gris d}"
    if !e.debloque.isEmpty then
      IO.println (jaune s!"🔑 Débloque : {", ".intercalate e.debloque.toList}")
    if e.celebre != 0 then
      IO.println (jaune s!"🏆 Théorème n°{e.celebre} de la liste des « 100 théorèmes célèbres » (Freek Wiedijk)")
    IO.println ""
    IO.println e.enonce
    if let some s := c.etat.get e.id then
      if s.message != "" then
        IO.println ""
        IO.println s.message
    IO.println (gris s!"\nIndices disponibles : {e.indices.size} (`./parcours indice {e.id}`)")

def cmdIndice (c : Ctx) (q : String) : IO Unit := do
  match trouverExo c.graphe q with
  | .error m => IO.println m
  | .ok e =>
    if e.indices.isEmpty then
      IO.println "Pas d'indice pour cet exercice. Courage !"
      return
    let rev ← lireReveles c
    let n := (rev.exos.find? (·.1 == e.id)).map (·.2) |>.getD 0
    let n' := min e.indices.size (n + 1)
    IO.println (gras s!"💡 Indices pour « {e.titre} » ({n'}/{e.indices.size}) :")
    for i in [0:n'] do
      IO.println s!"  {i+1}. {e.indices[i]!}"
    if n' < e.indices.size then
      IO.println (gris s!"\nRelance la même commande pour l'indice suivant.")
    else
      IO.println (gris s!"\nC'était le dernier indice. Il reste `./parcours solution {e.id}`… en dernier recours !")
    let exos := (rev.exos.filter (·.1 != e.id)).push (e.id, n')
    ecrireJson (fichierReveles c) ({ exos } : Reveles)

def lireLigne : IO String := do
  let l ← (← IO.getStdin).getLine
  return l.trimAscii.toString

def cmdSolution (c : Ctx) (q : String) : IO Unit := do
  match trouverExo c.graphe q with
  | .error m => IO.println m
  | .ok e =>
    if e.solution == "" then
      if e.genre == "ouvert" then
        IO.println "♾️  C'est un problème OUVERT : personne au monde ne connaît la solution. Bonne chance !"
      else
        IO.println "💀 Pas de solution de référence pour ce boss : tu es seul·e face à lui. (Les indices restent là.)"
      return
    IO.print (jaune s!"⚠️  Afficher la solution de « {e.titre} » ? Tape « oui » pour confirmer : ")
    (← IO.getStdout).flush
    let r ← lireLigne
    if r.toLower != "oui" then
      IO.println "Sage décision. 💪"
      return
    let txt ← IO.FS.readFile (c.racine / e.solution)
    IO.println ""
    IO.println txt

def ouvrir (args : Array String) : IO Unit := do
  let _ ← IO.Process.output { cmd := "open", args }

def cmdOuvrir (c : Ctx) (q : String) : IO Unit := do
  match trouverExo c.graphe q with
  | .error m => IO.println m
  | .ok e =>
    let f := (c.racine / e.fichier).toString
    let out ← IO.Process.output { cmd := "open", args := #["-a", "Visual Studio Code", f] }
    if out.exitCode != 0 then ouvrir #[f]
    IO.println s!"Ouverture de {e.fichier}"

def cmdReset (c : Ctx) (q : String) : IO Unit := do
  match trouverExo c.graphe q with
  | .error m => IO.println m
  | .ok e =>
    let vierge := c.racine / ".parcours" / "vierges" / e.fichier
    if !(← vierge.pathExists) then
      IO.println "Pas de version d'origine pour cet exercice."
      return
    IO.print (jaune s!"⚠️  Effacer ton travail dans {e.fichier} et repartir de zéro ? Tape « oui » : ")
    (← IO.getStdout).flush
    if (← lireLigne).toLower != "oui" then
      IO.println "Rien n'a été modifié."
      return
    let dest := c.racine / e.fichier
    IO.FS.createDirAll (c.racine / ".parcours" / "sauvegardes")
    if ← dest.pathExists then
      IO.FS.writeFile (c.racine / ".parcours" / "sauvegardes" / (e.id ++ ".lean")) (← IO.FS.readFile dest)
    IO.FS.writeFile dest (← IO.FS.readFile vierge)
    IO.println s!"Remis à zéro (ancienne version sauvegardée dans .parcours/sauvegardes/{e.id}.lean)."

def cmdVerifier (c : Ctx) (ouvrirCarte : Bool := false) : IO Unit := do
  IO.println (gris "Compilation de tes exercices (lake build)…")
  let t0 ← IO.monoMsNow
  let rb ← lancerBuild c.racine "Exercices"
  let bloq := bloques c.graphe rb.echecs
  IO.println (gris "Analyse des preuves…")
  let etats ← analyserArbre c.racine c.graphe "Exercices" rb.echecs bloq
  let ancien := c
  let c := { c with etat := { exos := etats } }
  ecrireJson (c.racine / ".parcours" / "etat.json") c.etat
  let t1 ← IO.monoMsNow
  IO.println (gris s!"Vérifié en {(t1 - t0) / 1000}s.\n")
  -- Nouveautés
  let nouveaux := c.graphe.exercices.filter fun e =>
    e.genre != "cours" && estFini (c.statut e) && !estFini (ancien.statut e)
  let nouvPurs := c.graphe.exercices.filter fun e =>
    c.statut e == "pur" && ancien.statut e == "reussi"
  let debloques := c.graphe.exercices.filter fun e =>
    e.genre != "cours" && c.disponible e && !ancien.disponible e && !estFini (ancien.statut e)
  if !ancien.etat.exos.isEmpty then
    for e in nouveaux do
      IO.println (vert s!"🎉 Nouveau : {c.icone e} {e.titre}")
    for e in nouvPurs do
      IO.println (jaune s!"⭐ Devenu pur : {e.titre}")
    for e in debloques do
      IO.println (cyan s!"🎯 Débloqué : {e.titre}  {gris e.id}")
    if !(nouveaux.isEmpty && nouvPurs.isEmpty && debloques.isEmpty) then IO.println ""
  -- Exercices réussis mais non purs
  IO.println (resume c)
  IO.println ""
  afficherErreurs c
  for (id, msg) in rb.erreurs.toList.take 5 do
    IO.println (rouge s!"── {id} ──")
    IO.println (gris ((msg.splitOn "\n").take 12 |> "\n".intercalate))
  if !rb.erreurs.isEmpty then IO.println ""
  afficherDisponibles c
  let carte ← genererCarte c
  IO.println (gris s!"\nCarte mise à jour : {carte} (`./parcours carte` pour l'ouvrir)")
  if ouvrirCarte then ouvrir #[carte.toString]

/-! ## Commandes de développement (pour maintenir le parcours) -/

/-- Calcule les hash des énoncés depuis les solutions et vérifie qu'elles sont toutes correctes. -/
def cmdDevSolutions (c : Ctx) : IO UInt32 := do
  IO.println "Compilation des solutions…"
  let rb ← lancerBuild c.racine "Solutions" (silencieux := true)
  for (id, msg) in rb.erreurs do
    IO.println (rouge s!"── {id} ──\n{msg}")
  let bloq := bloques c.graphe rb.echecs
  let donnees ← chargerDonnees c.racine
  let mut mods : Array Import := #[]
  for e in c.graphe.exercices do
    if rb.echecs.contains e.id || bloq.contains e.id then continue
    mods := mods.push { module := modulePour "Solutions" e.id }
  initSearchPath (← findSysroot)
  let env ← importModules mods {} (loadExts := false)
  let mut hashes : Array Json := #[]
  let mut memo : NameMap Bool := {}
  let mut problemes := 0
  for e in c.graphe.exercices do
    if rb.echecs.contains e.id || bloq.contains e.id then
      IO.println (rouge s!"✖ {e.id} : ne compile pas{if bloq.contains e.id then " (dépendance)" else ""}")
      problemes := problemes + 1
      continue
    let some ev := donnees.exercices.find? (·.id == e.id) | continue
    for cible in ev.cibles do
      match env.find? cible.toName with
      | some ci => hashes := hashes.push (Json.mkObj [("cible", cible), ("hash", toString ci.type.hash)])
      | none =>
        IO.println (rouge s!"✖ {e.id} : cible {cible} introuvable")
        problemes := problemes + 1
    if e.genre == "cours" then continue
    let (r, m') := (analyserExo env donnees { ev with hashes := #[] }).run memo
    memo := m'
    let attendu := e.solution != ""
    if attendu && !r.pur then
      problemes := problemes + 1
      IO.println (rouge s!"✖ {e.id} : solution non pure ou incomplète")
      IO.println (r.message env donnees e.titre)
    else if attendu && !r.depsInachevees.isEmpty then
      problemes := problemes + 1
      IO.println (rouge s!"✖ {e.id} : dépend de résultats inachevés {r.depsInachevees}")
    else if !attendu && r.reussi then
      IO.println (jaune s!"? {e.id} : marqué sans solution mais la solution est complète")
  ecrireJson (c.racine / ".parcours" / "hashes.json") (Json.arr hashes)
  IO.println s!"{hashes.size} énoncés hachés, {problemes} problème(s)."
  return if problemes == 0 then 0 else 1

end ParcoursCli

open ParcoursCli in
def main (args : List String) : IO UInt32 := do
  let c ← chargerCtx
  match args with
  | [] | ["statut"] => cmdStatut c
  | ["verifier"] | ["vérifier"] | ["v"] => cmdVerifier c
  | ["arbre"] => cmdArbre c none
  | ["arbre", b] => cmdArbre c (some b)
  | ["branches"] => cmdBranches c
  | ["info", q] => cmdInfo c q
  | ["indice", q] => cmdIndice c q
  | ["solution", q] => cmdSolution c q
  | ["ouvrir", q] => cmdOuvrir c q
  | ["reset", q] => cmdReset c q
  | ["carte"] =>
    let f ← genererCarte c
    ouvrir #[f.toString]
  | ["dev-solutions"] => return ← cmdDevSolutions c
  | ["aide"] | ["help"] | ["--help"] | ["-h"] => IO.println aide
  | _ =>
    IO.println "Commande inconnue."
    IO.println aide
    return 1
  return 0
