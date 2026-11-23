import Exercices.Tris.Definitions

/-!
# L'échiquier mutilé

On retire deux coins **opposés** d'un échiquier 8×8. Peut-on recouvrir les 62 cases restantes
avec 31 dominos (chaque domino couvre deux cases adjacentes) ?

Non ! Et la preuve tient en une idée : les deux coins retirés sont de la **même couleur**.
Un ordinateur qui chercherait par force brute mettrait un temps astronomique ; un argument de
coloriage règle la question. (Problème de Max Black, 1946, popularisé par Martin Gardner.)

Un pavage est une liste de dominos `(c, d)` de cases adjacentes, qui couvre chaque case
**exactement une fois** : la liste de toutes les cases couvertes est une **permutation** du plateau.

## À prouver
`echiquier_mutile : (∀ d ∈ dominos, Adjacentes d.1 d.2) → (dominos.flatMap (fun d => [d.1, d.2])).Perm plateau → False`

## Ressources
- [Problème de l'échiquier mutilé (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_de_l%27%C3%A9chiquier_mutil%C3%A9)

---
*Exercice* `Enigmes.Echiquier` · difficulté ★★★★☆

💡 Indices : `./parcours indice Enigmes.Echiquier` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

abbrev Case := Nat × Nat

/-- Les 62 cases : l'échiquier 8×8 privé des coins (0,0) et (7,7). -/
def plateau : List Case :=
  ((List.range 8).flatMap fun i => (List.range 8).map fun j => (i, j)).filter
    (fun c => c != (0, 0) && c != (7, 7))

def Adjacentes (c d : Case) : Prop :=
  (c.1 = d.1 ∧ (c.2 + 1 = d.2 ∨ d.2 + 1 = c.2)) ∨ (c.2 = d.2 ∧ (c.1 + 1 = d.1 ∨ d.1 + 1 = c.1))

def blanche (c : Case) : Bool := (c.1 + c.2) % 2 == 0

theorem compte (dominos : List (Case × Case)) (hadj : ∀ d ∈ dominos, Adjacentes d.1 d.2)
    (p : Case → Bool) (hp : ∀ c d, Adjacentes c d → p c = !p d) :
    (dominos.flatMap (fun d => [d.1, d.2])).countP p = dominos.length := by
  sorry

theorem echiquier_mutile (dominos : List (Case × Case)) (hadj : ∀ d ∈ dominos, Adjacentes d.1 d.2)
    (hpavage : (dominos.flatMap (fun d => [d.1, d.2])).Perm plateau) : False := by
  sorry

end Parcours.Enigmes

#verifier
