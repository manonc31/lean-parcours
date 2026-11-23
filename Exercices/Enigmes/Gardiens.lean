import Exercices.Logique.Bilan

/-!
# Les deux gardiens

Deux portes : l'une mène au trésor, l'autre au précipice. Deux gardiens : l'un dit **toujours**
la vérité, l'autre ment **toujours**, et tu ne sais pas lequel est lequel. Tu as droit à **une**
question à **un** gardien. Laquelle ?

Réponse célèbre : montre une porte et demande « Si je demandais à l'autre gardien si cette porte
mène au trésor, que me répondrait-il ? » … et fais le contraire ! Autre solution : « Si je te
demandais si cette porte mène au trésor, que me répondrais-tu ? » Là, la réponse est la vérité.

`repond h p` : la réponse (oui/non) d'un gardien d'honnêteté `h` à une question dont la vraie
réponse est `p`.

## À prouver
1. `demander_a_l_autre : repond h (repond (!h) t) = !t` (la réponse est toujours fausse)
2. `demander_a_soi : repond h (repond h t) = t` (la réponse est toujours juste)

---
*Exercice* `Enigmes.Gardiens` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Enigmes.Gardiens` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

def repond (honnete p : Bool) : Bool := if honnete then p else !p

theorem demander_a_l_autre (h t : Bool) : repond h (repond (!h) t) = !t := by
  sorry

theorem demander_a_soi (h t : Bool) : repond h (repond h t) = t := by
  sorry

end Parcours.Enigmes

#verifier
