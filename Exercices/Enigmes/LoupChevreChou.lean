import Exercices.Logique.Bilan

/-!
# Le loup, la chèvre et le chou

Un fermier doit faire traverser une rivière à un loup, une chèvre et un chou. Sa barque ne peut
porter que lui et **un** passager. Il ne faut jamais laisser seuls le loup et la chèvre (elle serait
mangée), ni la chèvre et le chou. Énigme d'Alcuin d'York (VIIIᵉ siècle) !

Un état indique la rive (`false` = départ, `true` = arrivée) du fermier, du loup, de la chèvre
et du chou. Trouve une suite d'états valide, de « tous au départ » à « tous à l'arrivée ».

## À faire
`solution : List Etat` (à écrire !) et `solution_valide : Valide solution = true`

---
*Exercice* `Enigmes.LoupChevreChou` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Enigmes.LoupChevreChou` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

/-- (fermier, loup, chèvre, chou) : `false` = rive de départ, `true` = rive d'arrivée. -/
abbrev Etat := Bool × Bool × Bool × Bool

def sur (e : Etat) : Bool :=
  let (f, l, c, x) := e
  !(l == c && f != c) && !(c == x && f != c)

/-- Le fermier traverse, seul ou avec un passager qui était sur sa rive. -/
def traversee (e e' : Etat) : Bool :=
  let (f, l, c, x) := e
  let (f', l', c', x') := e'
  f' != f &&
    ((l' == l && c' == c && x' == x) ||
     (l == f && l' == f' && c' == c && x' == x) ||
     (c == f && c' == f' && l' == l && x' == x) ||
     (x == f && x' == f' && l' == l && c' == c))

def chemin : List Etat → Bool
  | [] => true
  | [e] => sur e
  | e :: e' :: r => sur e && traversee e e' && chemin (e' :: r)

def Valide (s : List Etat) : Bool :=
  s.head? == some (false, false, false, false) && s.getLast? == some (true, true, true, true) && chemin s

def solution : List Etat :=
  sorry

theorem solution_valide : Valide solution = true := by
  sorry

end Parcours.Enigmes

#verifier
