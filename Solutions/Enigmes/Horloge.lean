/- @parcours
titre: Les aiguilles de l'horloge
difficulte: 2
requiert: Enigmes.Calendrier
indice: `omega` sait raisonner sur `%` par une constante.
indice: Le comptage est un calcul : `decide +kernel`.
-/
import Solutions.Listes.Pont
import Solutions.Recurrence.Definitions

/-!
# Les aiguilles de l'horloge

Combien de fois les deux aiguilles d'une horloge se superposent-elles en 12 heures ?
Pas 12, mais **11** ! La grande aiguille va 12 fois plus vite que la petite ; elle la rattrape
toutes les `12/11` heures, soit toutes les 1 h 05 min 27 s environ.

Pour rester dans les entiers, le temps `t` est compté en onzièmes de minute (12 heures = 7920
unités). La petite aiguille est à la graduation `t` (sur 7920), la grande à `12 t` (modulo 7920).

## À prouver
1. `superposees : t < 7920 → ((12 * t) % 7920 = t ↔ t % 720 = 0)`
2. `onze_fois` : il y a exactement 11 instants de superposition.
-/

namespace Parcours.Enigmes

theorem superposees (t : Nat) (h : t < 7920) : (12 * t) % 7920 = t ↔ t % 720 = 0 := by -- @exo
  omega

theorem onze_fois : ((List.range 7920).filter fun t => (12 * t) % 7920 == t).length = 11 := by -- @exo
  decide +kernel

end Parcours.Enigmes

#verifier
