import ParcoursOutils.Analyse
import Lean.Elab.Command
/-!
# La commande `#verifier`

Placée à la fin de chaque exercice, elle affiche dans l'éditeur (infoview)
si l'exercice est réussi, s'il est « pur » (⭐), et sinon ce qui manque.
-/
open Lean Elab Command

namespace ParcoursOutils

/-- Vérifie l'exercice du fichier courant et affiche le résultat. -/
syntax (name := verifierCmd) "#verifier" : command

@[command_elab verifierCmd] def elabVerifier : CommandElab := fun _ => do
  let fichier ← getFileName
  let chemin ← IO.FS.realPath fichier
  let some racine ← trouverRacine (chemin.parent.getD ".")
    | logWarning "#verifier : impossible de trouver la racine du parcours (.parcours/verif.json)."
  let racine ← IO.FS.realPath racine
  let d ← chargerDonnees racine
  let rel := (chemin.toString.drop (racine.toString.length + 1)).toString
  let some (_, id) := idDepuisChemin (rel.splitOn "/")
    | logInfo "#verifier : ce fichier ne fait pas partie du parcours."
  let some exo := d.exercices.find? (·.id == id)
    | logInfo s!"#verifier : « {id} » n'est pas un exercice connu du parcours."
  let env ← getEnv
  let (r, _) := (analyserExo env d exo).run {}
  let msg := r.message env d exo.titre
  if r.cibles.any (·.statut == .enonceModifie) then logWarning msg else logInfo msg

end ParcoursOutils
