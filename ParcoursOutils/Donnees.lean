import Lean.Data.Json
import Lean.Elab.Deriving.FromToJson
/-!
# Données du parcours

Lecture du fichier `.parcours/verif.json`, généré à partir des solutions.
Il contient, pour chaque exercice : les déclarations à prouver (« cibles »),
le hash de leur énoncé (pour détecter un énoncé modifié par erreur),
et les morceaux de la bibliothèque de Lean que l'exercice a le droit d'utiliser.
-/
open Lean

namespace ParcoursOutils

/-- Un « jeton » de déblocage : un ensemble de lemmes de la bibliothèque de Lean
que tu as le droit d'utiliser une fois que tu as refait le travail toi-même. -/
structure Jeton where
  nom : String
  description : String
  /-- Préfixes de noms concernés (`*` = tout). -/
  motifs : Array String
  /-- Préfixes exclus. -/
  sauf : Array String
  deriving FromJson, ToJson, Inhabited, Repr

/-- « Le jeton `jeton` est accordé par l'exercice `par`, s'il est terminé. » -/
structure Autorisation where
  jeton : String
  par : String
  deriving FromJson, ToJson, Inhabited, Repr

structure HashEnonce where
  cible : String
  hash : String
  deriving FromJson, ToJson, Inhabited, Repr

structure ExoVerif where
  id : String
  titre : String
  /-- Chemin relatif à la racine, ex. `Exercices/Naturels/AddComm.lean`. -/
  fichier : String
  cibles : Array String
  hashes : Array HashEnonce
  autorise : Array Autorisation
  interdit : Array String
  /-- Lemmes de la bibliothèque exceptionnellement permis dans cet exercice. -/
  permis : Array String
  debloque : Array String
  deriving FromJson, ToJson, Inhabited, Repr

structure DonneesVerif where
  base : Array String
  jetons : Array Jeton
  exercices : Array ExoVerif
  deriving FromJson, ToJson, Inhabited, Repr

def nomFichierVerif : System.FilePath := ".parcours" / "verif.json"

/-- Remonte l'arborescence depuis `depart` jusqu'à trouver la racine du parcours. -/
partial def trouverRacine (depart : System.FilePath) : IO (Option System.FilePath) := do
  let rec go (d : System.FilePath) (n : Nat) : IO (Option System.FilePath) := do
    if n == 0 then return none
    if ← (d / nomFichierVerif).pathExists then return some d
    match d.parent with
    | some p => if p == d then return none else go p (n - 1)
    | none => return none
  go depart 64

def chargerDonnees (racine : System.FilePath) : IO DonneesVerif := do
  let txt ← IO.FS.readFile (racine / nomFichierVerif)
  match Json.parse txt >>= fromJson? with
  | .ok d => return d
  | .error e => throw <| IO.userError s!"verif.json illisible : {e}"

/-- `Exercices/Naturels/AddComm.lean` ↦ (`Exercices`, `Naturels.AddComm`). -/
def idDepuisChemin (rel : List String) : Option (String × String) :=
  match rel with
  | arbre :: reste@(_ :: _) =>
    let reste := reste.mapIdx fun i s =>
      if i + 1 == reste.length then (s.dropSuffix ".lean").toString else s
    some (arbre, ".".intercalate reste)
  | _ => none

end ParcoursOutils
