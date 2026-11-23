import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fabrique import exo, ecrire_tout

RD = "Solutions.Recurrence.Definitions"
LP = "Solutions.Listes.Pont"
NS = "Parcours.Enigmes"

def en(ident, titre, diff, imports, texte, code, indices, requiert, ressources=()):
    exo("Enigmes", ident, titre, diff, imports, texte, code, indices, NS, requiert=requiert, ressources=ressources)

en("PoulesLapins", "Poules et lapins", 1, [RD],
"""Un vieux problème chinois (Sunzi, IIIᵉ siècle) : dans une basse-cour, on compte 35 têtes et
94 pattes. Combien de poules, combien de lapins ?

## Se le représenter
Imagine que tous les animaux lèvent deux pattes : il reste `2 × 35 = 70` pattes au sol. Les
`94 − 70 = 24` pattes levées en trop appartiennent aux lapins, qui en lèvent 2 chacun :
`12` lapins, donc `23` poules.

## À prouver
`poules_lapins : p + l = 35 → 2 * p + 4 * l = 94 → p = 23 ∧ l = 12`""",
"""theorem poules_lapins (p l : Nat) (htetes : p + l = 35) (hpattes : 2 * p + 4 * l = 94) :
    p = 23 ∧ l = 12 := by -- @exo
  omega""",
["`omega` résout les systèmes d'équations linéaires sur les entiers."], "Gymnase.Omega")

en("AneMulet", "L'âne et le mulet", 1, [RD],
"""Une énigme attribuée à Euclide : un âne et un mulet portent des sacs. L'âne se plaint de sa
charge. Le mulet lui dit : « Si tu me donnais un de tes sacs, j'en porterais deux fois plus que
toi ; si je t'en donnais un des miens, nous en porterions autant. » Combien portent-ils ?

## À prouver
`ane_mulet : m + 1 = 2 * (a - 1) → m - 1 = a + 1 → a = 5 ∧ m = 7`""",
"""theorem ane_mulet (a m : Nat) (h1 : m + 1 = 2 * (a - 1)) (h2 : m - 1 = a + 1) :
    a = 5 ∧ m = 7 := by -- @exo
  omega""",
["`omega`, même avec des soustractions (tronquées) sur `Nat`."], "Enigmes.PoulesLapins")

en("Escargot", "L'escargot dans le puits", 2, [RD],
"""Un escargot est au fond d'un puits de 10 mètres. Le jour, il monte de 3 mètres ; la nuit, il
glisse de 2 mètres. En combien de jours sort-il ? Pas 10 ! Le 8ᵉ jour, il part de 7 mètres et
atteint le bord avant de glisser.

`jours h f x` simule l'escargot dans un puits de hauteur `h`, parti le matin à la hauteur `x`
(avec au plus `f` jours de simulation).

## À prouver
1. `jours_spec` : dans un puits de `n + 3` mètres, l'escargot parti de `x` sort en `n − x + 1` jours.
2. `escargot : jours 10 8 0 = 8`""",
"""def jours (h : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, x => if h ≤ x + 3 then 1 else 1 + jours h f (x + 3 - 2)

theorem jours_spec (n f x : Nat) (hx : x ≤ n) (hf : n - x + 1 ≤ f) :
    jours (n + 3) f x = n - x + 1 := by -- @exo
  induction f generalizing x with
  | zero => omega
  | succ f ih =>
    simp only [jours]
    split
    · omega
    · have e : x + 3 - 2 = x + 1 := by omega
      rw [e, ih (x + 1) (by omega) (by omega)]
      omega

theorem escargot : jours 10 8 0 = 8 := by -- @exo
  exact jours_spec 7 8 0 (by omega) (by omega)""",
["Récurrence sur le nombre de jours `f`, en généralisant la hauteur du matin `x`.", "Dans le cas où l'escargot ne sort pas, `x + 3 - 2 = x + 1`."], "Enigmes.AneMulet")

en("CentOiseaux", "Les cent volailles", 2, [RD],
"""Un problème chinois du Vᵉ siècle (Zhang Qiujian) : un coq coûte 5 sapèques, une poule 3, et
on a 3 poussins pour 1 sapèque. Avec 100 sapèques, on achète exactement 100 volailles. Combien de
chaque ? Il y a **quatre** solutions !

En multipliant le prix par 3 pour éviter les fractions : `15c + 9p + q = 300`.

## À prouver
`cent_oiseaux` : les quatre solutions, et seulement elles.""",
"""def Achat (c p q : Nat) : Prop := c + p + q = 100 ∧ 15 * c + 9 * p + q = 300

theorem cent_oiseaux (c p q : Nat) : Achat c p q ↔
    (c = 0 ∧ p = 25 ∧ q = 75) ∨ (c = 4 ∧ p = 18 ∧ q = 78) ∨
    (c = 8 ∧ p = 11 ∧ q = 81) ∨ (c = 12 ∧ p = 4 ∧ q = 84) := by -- @exo
  unfold Achat
  omega""",
["En soustrayant les deux équations : `7c + 4p = 100`, donc `c` est multiple de 4.", "`omega` fait toute l'analyse tout seul (après `unfold Achat`)."], "Enigmes.PoulesLapins")

en("PagesLivre", "Les pages du livre", 2, [RD],
"""Pour numéroter les pages d'un livre (à partir de 1), un imprimeur a utilisé 1 095 chiffres.
Combien de pages a le livre ?

## Se le représenter
Pages 1 à 9 : 9 chiffres. Pages 10 à 99 : `90 × 2 = 180` chiffres. Ensuite, 3 chiffres par page :
`1095 − 189 = 906 = 3 × 302`. Donc `99 + 302 = 401` pages.

## À prouver
1. `croissant : chiffresLivre m ≤ chiffresLivre (m + k)`
2. `formule : chiffresLivre (99 + k) = 189 + 3k` (pour `k ≤ 900`)
3. `livre : chiffresLivre n = 1095 ↔ n = 401` (pour `n ≤ 999`)""",
"""def chiffresPage (p : Nat) : Nat := if p < 10 then 1 else if p < 100 then 2 else 3

def chiffresLivre : Nat → Nat
  | 0 => 0
  | n + 1 => chiffresLivre n + chiffresPage (n + 1)

theorem croissant (m k : Nat) : chiffresLivre m ≤ chiffresLivre (m + k) := by -- @exo
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    rw [← Nat.add_assoc, chiffresLivre]
    omega

theorem formule (k : Nat) (hk : k ≤ 900) : chiffresLivre (99 + k) = 189 + 3 * k := by -- @exo
  induction k with
  | zero => decide
  | succ k ih =>
    rw [← Nat.add_assoc, chiffresLivre, ih (by omega)]
    have : chiffresPage (99 + k + 1) = 3 := by
      unfold chiffresPage
      split
      · omega
      · split
        · omega
        · rfl
    omega

theorem livre (n : Nat) (hn : n ≤ 999) : chiffresLivre n = 1095 ↔ n = 401 := by -- @exo
  constructor
  · intro h
    by_cases h' : n < 99
    · have := croissant n (99 - n)
      rw [show n + (99 - n) = 99 by omega, show chiffresLivre 99 = 189 by decide] at this
      omega
    · have := formule (n - 99) (by omega)
      rw [show 99 + (n - 99) = n by omega] at this
      omega
  · rintro rfl
    exact formule 302 (by omega)""",
["`croissant` : récurrence sur `k`.", "`formule` : récurrence sur `k` ; la page `100 + k` a 3 chiffres.", "`livre` : si `n < 99`, le livre a au plus 189 chiffres ; sinon, utilise `formule (n - 99)`."], "Enigmes.CentOiseaux")

en("Bidons", "Les bidons de Die Hard", 2, [LP, RD],
"""Dans le film *Die Hard 3*, les héros doivent désamorcer une bombe en posant exactement 4 litres
d'eau sur une balance. Ils n'ont qu'un bidon de 3 litres, un bidon de 5 litres, et une fontaine.
On peut remplir un bidon, le vider, ou verser l'un dans l'autre (jusqu'à ce que l'un soit vide ou
l'autre plein).

## À faire
Écris `solutionBidons` (la liste des états successifs `(bidon de 3 L, bidon de 5 L)`, en partant
de `(0, 0)`) et vérifie-la avec `decide`.""",
"""/-- (contenu du petit bidon, contenu du grand). -/
abbrev Contenu := Nat × Nat

/-- Les états atteignables en un coup, avec des bidons de capacités `A` et `B`. -/
def suivants (A B : Nat) (e : Contenu) : List Contenu :=
  [(A, e.2), (e.1, B), (0, e.2), (e.1, 0),
   (e.1 - min e.1 (B - e.2), e.2 + min e.1 (B - e.2)),
   (e.1 + min e.2 (A - e.1), e.2 - min e.2 (A - e.1))]

def cheminBidons (A B : Nat) : List Contenu → Bool
  | e :: e' :: r => (suivants A B e).contains e' && cheminBidons A B (e' :: r)
  | _ => true

def Obtient (A B but : Nat) (s : List Contenu) : Bool :=
  s.head? == some (0, 0) && cheminBidons A B s &&
    s.getLast?.any (fun e => e.1 == but || e.2 == but)

def solutionBidons : List Contenu := -- @exo
  [(0, 0), (0, 5), (3, 2), (0, 2), (2, 0), (2, 5), (3, 4)]

theorem die_hard : Obtient 3 5 4 solutionBidons = true := by -- @exo
  decide""",
["Remplis le grand bidon, et verse-le dans le petit : il reste 2 litres dans le grand.", "Vide le petit, mets-y les 2 litres, remplis le grand, et complète le petit…"], "Enigmes.LoupChevreChou",
ressources=["[Problème des bidons (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_des_bidons)"])

en("BidonsImpossible", "Des bidons impossibles", 3, ["Solutions.Enigmes.Bidons"],
"""Avec un bidon de 6 litres et un bidon de 9 litres, peut-on obtenir 4 litres ? Non ! Quoi qu'on
fasse, chaque bidon contient toujours un **multiple de 3** litres : c'est un **invariant**.
(En général, on obtient exactement les multiples du PGCD des deux capacités.)

`Accessible A B e` : l'état `e` peut être atteint depuis `(0, 0)`.

## À prouver
1. `invariant : Accessible 6 9 e → e.1 % 3 = 0 ∧ e.2 % 3 = 0`
2. `jamais_quatre : Accessible 6 9 e → e.1 ≠ 4 ∧ e.2 ≠ 4`""",
"""inductive Accessible (A B : Nat) : Contenu → Prop
  | depart : Accessible A B (0, 0)
  | coup {e e' : Contenu} : Accessible A B e → e' ∈ suivants A B e → Accessible A B e'

theorem invariant (e : Contenu) (h : Accessible 6 9 e) : e.1 % 3 = 0 ∧ e.2 % 3 = 0 := by -- @exo
  induction h with
  | depart => decide
  | coup _ h ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [suivants, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; omega)

theorem jamais_quatre (e : Contenu) (h : Accessible 6 9 e) : e.1 ≠ 4 ∧ e.2 ≠ 4 := by -- @exo
  have := invariant e h
  omega""",
["Récurrence sur `h : Accessible 6 9 e` (`induction h`).", "Dans le cas `coup`, `e'` est l'un des 6 états de `suivants` : `simp only [suivants, List.mem_cons, …] at h` puis `rcases h with rfl | rfl | …`.", "`omega` connaît `min` et `%`."], "Enigmes.Bidons")

en("Missionnaires", "Missionnaires et cannibales", 2, [LP, RD],
"""Trois missionnaires et trois cannibales doivent traverser une rivière avec une barque à deux
places. Si, sur une rive, les cannibales sont plus nombreux que les missionnaires (et qu'il y a
au moins un missionnaire), ça se passe mal. Comment faire ?

Un état `(m, c, b)` : nombre de missionnaires et de cannibales sur la rive de **départ**, et
`b = true` si la barque y est.

## À faire
1. Écris `solutionMC` et prouve `solutionMC_ok`.
2. `pas_moins_de_11` : impossible en moins de 11 traversées (l'ensemble des états atteints en au
   plus 10 traversées ne contient pas l'arrivée).""",
"""abbrev Rive := Nat × Nat × Bool

def rivesSures (e : Rive) : Bool :=
  let (m, c, _) := e
  m ≤ 3 && c ≤ 3 && (m == 0 || c ≤ m) && (m == 3 || 3 - c ≤ 3 - m)

def apres (e : Rive) (p : Nat × Nat) : Option Rive :=
  let (m, c, b) := e
  if b then (if p.1 ≤ m && p.2 ≤ c then some (m - p.1, c - p.2, false) else none)
  else (if p.1 + m ≤ 3 && p.2 + c ≤ 3 then some (m + p.1, c + p.2, true) else none)

def voisinsMC (e : Rive) : List Rive :=
  ([(1, 0), (2, 0), (0, 1), (0, 2), (1, 1)].filterMap (apres e)).filter rivesSures

def cheminMC : List Rive → Bool
  | e :: e' :: r => (voisinsMC e).contains e' && cheminMC (e' :: r)
  | _ => true

def ValideMC (s : List Rive) : Bool :=
  s.head? == some (3, 3, true) && s.getLast? == some (0, 0, false) && cheminMC s

def solutionMC : List Rive := -- @exo
  [(3, 3, true), (3, 1, false), (3, 2, true), (3, 0, false), (3, 1, true), (1, 1, false),
   (2, 2, true), (0, 2, false), (0, 3, true), (0, 1, false), (1, 1, true), (0, 0, false)]

theorem solutionMC_ok : ValideMC solutionMC = true := by -- @exo
  decide

/-- Les états atteints en au plus `k` traversées. -/
def atteints : Nat → List Rive
  | 0 => [(3, 3, true)]
  | k + 1 => ((atteints k).flatMap voisinsMC ++ atteints k).eraseDups

theorem pas_moins_de_11 : (atteints 10).contains (0, 0, false) = false := by -- @exo
  decide""",
["Commence par faire passer deux cannibales, puis un revient…", "Le moment délicat : faire passer deux missionnaires au milieu.", "`pas_moins_de_11` est un calcul : `decide`."], "Enigmes.Bidons",
ressources=["[Problème des missionnaires et des cannibales (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_des_missionnaires_et_des_cannibales)"])

en("PontTorche", "Le pont et la lampe", 2, [LP, RD],
"""Quatre personnes doivent traverser un pont de nuit, avec une seule lampe. Le pont supporte au
plus deux personnes, et il faut la lampe pour traverser. Elles mettent 1, 2, 5 et 10 minutes ;
à deux, on va au rythme du plus lent. La lampe doit être rapportée à chaque fois.
Peut-on traverser en 17 minutes ? (Indice : ce n'est pas en faisant tout raccompagner par le plus
rapide, qui donne 19 minutes.)

Chaque personne est désignée par son temps. Une stratégie est la liste des groupes qui traversent,
alternativement à l'aller et au retour.

## À faire
1. Écris `solutionPont` et prouve `dix_sept : traverser [1, 2, 5, 10] [] true solutionPont = some 17`.
2. `optimal` : la recherche exhaustive parmi toutes les stratégies en 5 traversées (le minimum
   pour 4 personnes) ne fait pas mieux que 17.""",
"""/-- `traverser gauche droite aller groupes` : le temps total, ou `none` si la stratégie est invalide. -/
def traverser : List Nat → List Nat → Bool → List (List Nat) → Option Nat
  | g, _, _, [] => if g.isEmpty then some 0 else none
  | g, d, aller, grp :: r =>
    if (grp.length == 1 || grp.length == 2) && grp.eraseDups == grp &&
        grp.all ((if aller then g else d).contains ·) then
      (if aller then traverser (g.removeAll grp) (d ++ grp) false r
       else traverser (g ++ grp) (d.removeAll grp) true r).map (grp.foldl max 0 + ·)
    else none

def solutionPont : List (List Nat) := -- @exo
  [[1, 2], [1], [5, 10], [2], [1, 2]]

theorem dix_sept : traverser [1, 2, 5, 10] [] true solutionPont = some 17 := by -- @exo
  decide

/-- Pour la recherche exhaustive, on code un groupe de personnes par un nombre binaire (un
« masque ») : le bit 0 pour la personne de 1 min, le bit 1 pour 2 min, le bit 2 pour 5 min,
le bit 3 pour 10 min. `tempsGroupe` donne le temps de traversée d'un groupe. -/
def tempsGroupe : Nat → Nat
  | 1 => 1 | 2 => 2 | 4 => 5 | 8 => 10
  | 3 => 2 | 5 => 5 | 6 => 5 | 9 => 10 | 10 => 10 | 12 => 10
  | _ => 0

def groupesMasques : List Nat := [1, 2, 4, 8, 3, 5, 6, 9, 10, 12]

/-- Le meilleur temps en au plus `f` traversées, si le masque `g` est sur la rive de départ. -/
def meilleur : Nat → Nat → Bool → Option Nat
  | _, 0, _ => some 0
  | 0, _, _ => none
  | f + 1, g, aller =>
    (groupesMasques.filterMap fun grp =>
      if grp &&& (if aller then g else 15 - g) == grp then
        (meilleur f (if aller then g - grp else g + grp) (!aller)).map (tempsGroupe grp + ·)
      else none).min?

theorem optimal : meilleur 5 15 true = some 17 := by -- @exo
  decide +kernel""",
["L'astuce : faire traverser **ensemble** les deux plus lents (5 et 10).", "Pour que ce soit possible, il faut qu'un rapide soit déjà de l'autre côté pour ramener la lampe."], "Enigmes.Missionnaires",
ressources=["[Le problème du pont et de la torche (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Bridge_and_torch_problem)"])

en("Vendredi13", "Il y a un vendredi 13 chaque année", 1, [LP, RD],
"""Chaque année, il y a au moins un vendredi 13, et au plus trois. Pourquoi ? Le jour de la
semaine du 13 de chaque mois ne dépend que du jour de la semaine du 13 janvier et de l'année
(bissextile ou non) ; et les 12 mois couvrent forcément les 7 jours de la semaine.

Les jours sont numérotés `0` (lundi) à `6` (dimanche) : vendredi = 4.

## À prouver
1. `au_moins_un : ∀ d < 7, ∀ b, 4 ∈ treizes d b`
2. `au_plus_trois : ∀ d < 7, ∀ b, (treizes d b).count 4 ≤ 3`""",
"""def longueursMois (bissextile : Bool) : List Nat :=
  [31, if bissextile then 29 else 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]

/-- Le jour de la semaine du 13 de chaque mois, si le 13 janvier tombe le jour `d`. -/
def treizes (d : Nat) (b : Bool) : List Nat :=
  (List.range 12).map fun k => (d + ((longueursMois b).take k).sum) % 7

theorem au_moins_un : ∀ d, d < 7 → ∀ b : Bool, 4 ∈ treizes d b := by -- @exo
  decide

theorem au_plus_trois : ∀ d, d < 7 → ∀ b : Bool, (treizes d b).count 4 ≤ 3 := by -- @exo
  decide""",
["Il n'y a que 14 cas (7 jours × bissextile ou non) : `decide`.", "Essaie `#eval treizes 0 false` pour voir les jours de la semaine des 13 en 2025."], "Enigmes.PoulesLapins")

en("Calendrier", "Le calendrier perpétuel", 2, [LP, RD],
"""La **congruence de Zeller** donne le jour de la semaine de n'importe quelle date (calendrier
grégorien) : `0` = samedi, `1` = dimanche, `2` = lundi, `3` = mardi… Janvier et février comptent
comme les mois 13 et 14 de l'année précédente (pour que le 29 février soit à la fin).

## À prouver
1. `bastille` : le 14 juillet 1789 était un mardi.
2. `an_2000` : le 1ᵉʳ janvier 2000 était un samedi.
3. `periode : zeller j m (a + 400) = zeller j m a` : le calendrier se répète tous les 400 ans.""",
"""def zeller (jour mois annee : Nat) : Nat :=
  let m := if mois ≤ 2 then mois + 12 else mois
  let a := if mois ≤ 2 then annee - 1 else annee
  (jour + 13 * (m + 1) / 5 + a % 100 + a % 100 / 4 + a / 100 / 4 + 5 * (a / 100)) % 7

theorem bastille : zeller 14 7 1789 = 3 := by -- @exo
  decide

theorem an_2000 : zeller 1 1 2000 = 0 := by -- @exo
  decide

theorem periode (j m a : Nat) (ha : 1 ≤ a) : zeller j m (a + 400) = zeller j m a := by -- @exo
  have cle : ∀ x : Nat, (x + 400) % 100 = x % 100 ∧ (x + 400) / 100 / 4 = x / 100 / 4 + 1 ∧
      5 * ((x + 400) / 100) = 5 * (x / 100) + 20 := by
    intro x
    omega
  unfold zeller
  by_cases h : m ≤ 2 <;> simp only [h, ↓reduceIte]
  · rw [show a + 400 - 1 = (a - 1) + 400 by omega]
    obtain ⟨k1, k2, k3⟩ := cle (a - 1)
    rw [k1, k2, k3]
    omega
  · obtain ⟨k1, k2, k3⟩ := cle a
    rw [k1, k2, k3]
    omega""",
["Pour les dates : `decide`.", "Pour `periode` : `unfold zeller`, `by_cases h : m ≤ 2` (janvier-février ou non), `simp only [h, ↓reduceIte]`. `omega` a besoin d'aide : prouve d'abord que `(x + 400) % 100 = x % 100` et `(x + 400) / 100 / 4 = x / 100 / 4 + 1`, et réécris avec (`a % 100` ne change pas, `a / 100` augmente de 4)."], "Enigmes.Vendredi13",
ressources=["[Congruence de Zeller (Wikipédia)](https://fr.wikipedia.org/wiki/Congruence_de_Zeller)"])

en("Horloge", "Les aiguilles de l'horloge", 2, [LP, RD],
"""Combien de fois les deux aiguilles d'une horloge se superposent-elles en 12 heures ?
Pas 12, mais **11** ! La grande aiguille va 12 fois plus vite que la petite ; elle la rattrape
toutes les `12/11` heures, soit toutes les 1 h 05 min 27 s environ.

Pour rester dans les entiers, le temps `t` est compté en onzièmes de minute (12 heures = 7920
unités). La petite aiguille est à la graduation `t` (sur 7920), la grande à `12 t` (modulo 7920).

## À prouver
1. `superposees : t < 7920 → ((12 * t) % 7920 = t ↔ t % 720 = 0)`
2. `onze_fois` : il y a exactement 11 instants de superposition.""",
"""theorem superposees (t : Nat) (h : t < 7920) : (12 * t) % 7920 = t ↔ t % 720 = 0 := by -- @exo
  omega

theorem onze_fois : ((List.range 7920).filter fun t => (12 * t) % 7920 == t).length = 11 := by -- @exo
  decide +kernel""",
["`omega` sait raisonner sur `%` par une constante.", "Le comptage est un calcul : `decide +kernel`."], "Enigmes.Calendrier")

en("Nombre1089", "Le tour du 1089", 1, [RD],
"""Un tour de magie : pense à un nombre de 3 chiffres dont le premier chiffre est plus grand que le
dernier (par exemple 732). Retourne-le (237) et soustrais : `732 − 237 = 495`. Retourne le
résultat (594) et ajoute : `495 + 594 = 1089`. Quel que soit ton nombre, tu trouves **1089** !

(Les nombres comme 99 s'écrivent 099 sur trois chiffres.)

## À prouver
`tour_1089 : n < 1000 → n % 10 < n / 100 → tour1089 n = 1089`""",
"""def renverser3 (n : Nat) : Nat := (n % 10) * 100 + (n / 10 % 10) * 10 + n / 100

def tour1089 (n : Nat) : Nat := (n - renverser3 n) + renverser3 (n - renverser3 n)

theorem tour_1089 : ∀ n, n < 1000 → n % 10 < n / 100 → tour1089 n = 1089 := by -- @exo
  decide +kernel""",
["Calcul sur les 1000 nombres : `decide +kernel`.", "Pour comprendre : avec les chiffres `a > c`, la différence vaut `99 (a − c)`, donc ses chiffres sont `a − c − 1`, `9`, `10 − (a − c)`."], "Enigmes.PoulesLapins")

en("Cyclique", "Le nombre cyclique 142857", 1, [RD],
"""`142857 × 2 = 285714`, `× 3 = 428571`, `× 4 = 571428`, `× 5 = 714285`, `× 6 = 857142` : toujours
les mêmes chiffres, qui **tournent** ! Et `142857 × 7 = 999999`. Le secret : `1/7 = 0,142857142857…`

## À prouver
1. `rotations` : pour `k` de 1 à 6, les chiffres de `142857 × k` sont une rotation de ceux de 142857.
2. `fois_sept : 142857 * 7 = 999999`""",
"""def chiffres6 (n : Nat) : List Nat :=
  [n / 100000 % 10, n / 10000 % 10, n / 1000 % 10, n / 100 % 10, n / 10 % 10, n % 10]

theorem rotations : ∀ k, k < 6 → ∃ r, r < 6 ∧ chiffres6 (142857 * (k + 1)) = (chiffres6 142857).rotateLeft r := by -- @exo
  decide

theorem fois_sept : 142857 * 7 = 999999 := by -- @exo
  decide""",
["`decide` sait vérifier un `∃ r, r < 6 ∧ …` (il essaie les 6 valeurs)."], "Enigmes.Nombre1089")

en("PoidsBachet", "Les poids de Bachet", 2, [LP, RD],
"""Avec seulement 4 poids, de 1, 3, 9 et 27 grammes, on peut peser **toutes** les masses entières
de 1 à 40 grammes, à condition de pouvoir poser des poids sur **les deux** plateaux de la balance
(Bachet de Méziriac, 1624). Avec un seul plateau, il faut les puissances de 2 : 1, 2, 4, 8, 16, 32
permettent de peser de 0 à 63.

## À prouver
1. `bachet_quarante` : tout `n ≤ 40` est pesable avec 1, 3, 9, 27 (deux plateaux).
2. `binaire_63` : tout `n < 64` est pesable avec 1, 2, 4, 8, 16, 32 (un plateau).""",
"""/-- Les masses pesables : chaque poids est à gauche (`−`), absent, ou à droite (`+`). -/
def pesables : List Nat → List Int
  | [] => [0]
  | p :: ps => (pesables ps).flatMap fun m => [m - p, m, m + p]

/-- Les masses pesables avec un seul plateau. -/
def sommes : List Nat → List Nat
  | [] => [0]
  | p :: ps => (sommes ps).flatMap fun m => [m, m + p]

theorem bachet_quarante : ∀ n : Nat, n < 41 → (n : Int) ∈ pesables [1, 3, 9, 27] := by -- @exo
  decide +kernel

theorem binaire_63 : ∀ n, n < 64 → n ∈ sommes [1, 2, 4, 8, 16, 32] := by -- @exo
  decide +kernel""",
["Ce sont des vérifications exhaustives : `decide +kernel`.", "Pour comprendre : c'est l'écriture des nombres en base 3 avec les chiffres −1, 0, 1."], "Enigmes.Cyclique",
ressources=["[Problème des poids de Bachet (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_des_poids_de_Bachet)"])

en("Jeu24", "Le jeu de 24", 2, [LP, RD],
"""Avec quatre cartes, obtenir 24 en utilisant chaque carte exactement une fois et les opérations
`+ − × ÷` (divisions exactes seulement). Par exemple, avec 1, 2, 3, 4 : `1 × 2 × 3 × 4 = 24`.

## À faire
Écris les calculs `partie1` à `partie4`, pour les cartes :
1. `[4, 7, 8, 8]`
2. `[3, 3, 3, 3]`
3. `[5, 5, 5, 5]`
4. `[10, 10, 4, 4]`
puis prouve `tout_reussi`.""",
"""inductive Calcul where
  | nb (k : Nat)
  | plus (a b : Calcul)
  | moins (a b : Calcul)
  | fois (a b : Calcul)
  | divise (a b : Calcul)

def Calcul.val : Calcul → Option Nat
  | .nb k => some k
  | .plus a b => do return (← a.val) + (← b.val)
  | .moins a b => do
    let x ← a.val
    let y ← b.val
    if y ≤ x then some (x - y) else none
  | .fois a b => do return (← a.val) * (← b.val)
  | .divise a b => do
    let x ← a.val
    let y ← b.val
    if y ≠ 0 ∧ x % y = 0 then some (x / y) else none

def Calcul.cartes : Calcul → List Nat
  | .nb k => [k]
  | .plus a b => a.cartes ++ b.cartes
  | .moins a b => a.cartes ++ b.cartes
  | .fois a b => a.cartes ++ b.cartes
  | .divise a b => a.cartes ++ b.cartes

def Reussi (c : Calcul) (main : List Nat) : Bool := c.val == some 24 && c.cartes.isPerm main

open Calcul in
def partie1 : Calcul := -- @exo
  fois (moins (nb 7) (divise (nb 8) (nb 8))) (nb 4)

open Calcul in
def partie2 : Calcul := -- @exo
  moins (fois (fois (nb 3) (nb 3)) (nb 3)) (nb 3)

open Calcul in
def partie3 : Calcul := -- @exo
  moins (fois (nb 5) (nb 5)) (divise (nb 5) (nb 5))

open Calcul in
def partie4 : Calcul := -- @exo
  divise (moins (fois (nb 10) (nb 10)) (nb 4)) (nb 4)

theorem tout_reussi : Reussi partie1 [4, 7, 8, 8] && Reussi partie2 [3, 3, 3, 3] &&
    Reussi partie3 [5, 5, 5, 5] && Reussi partie4 [10, 10, 4, 4] = true := by -- @exo
  decide""",
["`[4, 7, 8, 8]` : que vaut `8 / 8` ?", "`[5, 5, 5, 5]` : `5 × 5 = 25`, et il faut enlever 1…", "`[10, 10, 4, 4]` : `10 × 10 − 4 = 96 = 4 × 24`."], "Enigmes.SendMoreMoney",
ressources=["[Jeu de 24 (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/24_(puzzle))"])

en("VingtEtUnCartes", "Le tour des 21 cartes", 2, [LP, RD],
"""Un tour de magie classique (déjà décrit par Gergonne en 1813) : le magicien distribue 21 cartes
en trois tas, le spectateur indique le tas qui contient sa carte, et le magicien ramasse les tas en
mettant celui-là **au milieu**. Après trois distributions, la carte choisie est toujours la
**onzième** !

## Se le représenter
Si la carte est en position `p` (de 0 à 20), elle se retrouve dans le tas `p % 3` en position
`p / 3`, et après ramassage en position `7 + p / 3`. Partant de `p ≤ 20` : après un tour,
`7 ≤ p ≤ 13` ; après deux, `9 ≤ p ≤ 11` ; après trois, `p = 10`.

## À prouver
1. `onzieme` : la simulation avec de vraies listes.
2. `position` : le calcul sur les positions.""",
"""/-- Distribue les cartes une par une sur trois tas. -/
def distribuer {α : Type} : List α → List α × List α × List α
  | a :: b :: c :: r =>
    let t := distribuer r
    (a :: t.1, b :: t.2.1, c :: t.2.2)
  | [a, b] => ([a], [b], [])
  | [a] => ([a], [], [])
  | [] => ([], [], [])

/-- Ramasse les tas en mettant au milieu celui qui contient la carte `c`. -/
def ramasser (c : Nat) (t : List Nat × List Nat × List Nat) : List Nat :=
  if t.1.contains c then t.2.1 ++ t.1 ++ t.2.2
  else if t.2.1.contains c then t.1 ++ t.2.1 ++ t.2.2
  else t.1 ++ t.2.2 ++ t.2.1

def unTour (c : Nat) (paquet : List Nat) : List Nat := ramasser c (distribuer paquet)

theorem onzieme : ∀ c, c < 21 → (unTour c (unTour c (unTour c (List.range 21)))).idxOf c = 10 := by -- @exo
  decide +kernel

theorem position (p : Nat) (h : p < 21) : 7 + (7 + (7 + p / 3) / 3) / 3 = 10 := by -- @exo
  omega""",
["`onzieme` : un calcul, `decide +kernel`.", "`position` : `omega`."], "Enigmes.Nombre1089",
ressources=["[Tour de cartes de Gergonne (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Gergonne%27s_three_pile_problem)"])

en("Cavalier", "Le tour du cavalier", 2, [LP, RD],
"""Un cavalier d'échecs peut-il visiter **toutes** les cases d'un échiquier, chacune une seule fois ?
Euler s'y est intéressé en 1759. Sur un échiquier 5 × 5, c'est possible en partant d'un coin.
Sur un 3 × 3, c'est impossible : la case centrale est inaccessible !

Les cases d'un échiquier `n × n` sont numérotées de `0` à `n² − 1` (ligne par ligne).

## À faire
1. Écris `tour5` (un tour du cavalier sur l'échiquier 5 × 5) et prouve `tour5_ok`.
2. `centre_isole` : sur l'échiquier 3 × 3, aucun saut ne mène à la case centrale (4).""",
"""def saut (n a b : Nat) : Bool :=
  let x := a / n
  let y := a % n
  let x' := b / n
  let y' := b % n
  ((x + 1 == x' || x' + 1 == x) && (y + 2 == y' || y' + 2 == y)) ||
    ((x + 2 == x' || x' + 2 == x) && (y + 1 == y' || y' + 1 == y))

def sauts (n : Nat) : List Nat → Bool
  | a :: b :: r => saut n a b && sauts n (b :: r)
  | _ => true

def TourCavalier (n : Nat) (l : List Nat) : Bool :=
  l.length == n * n && l.all (· < n * n) && l.eraseDups.length == n * n && sauts n l

def tour5 : List Nat := -- @exo
  [0, 7, 4, 13, 24, 17, 20, 11, 18, 9, 2, 5, 16, 23, 14, 3, 6, 15, 22, 19, 8, 1, 12, 21, 10]

theorem tour5_ok : TourCavalier 5 tour5 = true := by -- @exo
  decide

theorem centre_isole : ∀ b, b < 9 → saut 3 b 4 = false := by -- @exo
  decide""",
["**Règle de Warnsdorff** : va toujours vers la case qui a le moins de sorties encore libres.", "Commence par le coin 0 ; les cases voisines du coin sont 7 et 11."], "Enigmes.Echiquier",
ressources=["[Problème du cavalier (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_du_cavalier)"])

en("Sudoku", "Un petit sudoku", 1, [LP, RD],
"""Un sudoku 4 × 4 : chaque ligne, chaque colonne et chaque bloc 2 × 2 contient 1, 2, 3, 4.
La grille est lue ligne par ligne (cases 0 à 15). Les indices sont donnés sous la forme
`(case, valeur)`.

```
. 2 | . .
. . | 1 .
----+----
. 1 | . .
. . | 2 .
```

## À faire
Complète `maGrille` et prouve `maGrille_ok`.""",
"""def groupesSudoku : List (List Nat) :=
  [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13, 14, 15],
   [0, 4, 8, 12], [1, 5, 9, 13], [2, 6, 10, 14], [3, 7, 11, 15],
   [0, 1, 4, 5], [2, 3, 6, 7], [8, 9, 12, 13], [10, 11, 14, 15]]

def GrilleOk (g : List Nat) : Bool :=
  g.length == 16 && g.all (fun x => 1 ≤ x && x ≤ 4) &&
    groupesSudoku.all fun gr => (gr.map (g.getD · 0)).eraseDups.length == 4

def indicesSudoku : List (Nat × Nat) := [(1, 2), (6, 1), (9, 1), (14, 2)]

def maGrille : List Nat := -- @exo
  [1, 2, 3, 4,
   3, 4, 1, 2,
   2, 1, 4, 3,
   4, 3, 2, 1]

theorem maGrille_ok : GrilleOk maGrille && indicesSudoku.all (fun p => maGrille.getD p.1 0 == p.2) = true := by -- @exo
  decide""",
["Case 0 : la ligne 0 contient déjà un 2, la colonne 0… commence par les cases les plus contraintes.", "Il y a plusieurs solutions possibles : n'importe laquelle convient !"], "Enigmes.CarreMagique")

en("QuiPoisson", "Qui a le poisson ?", 2, [LP, RD],
"""Une version miniature de la célèbre « énigme d'Einstein ». Alice, Bob, Chloé et David habitent
quatre maisons alignées (dans cet ordre). Chacun a un animal (chat, chien, poisson, lapin) et une
maison d'une couleur (rouge, verte, bleue, jaune), tous différents.

1. Alice n'a pas le chat.
2. Bob habite la maison rouge.
3. Le chien habite la maison bleue.
4. Chloé n'a ni le poisson ni le chat.
5. La maison d'Alice n'est pas verte.
6. Le chat est le voisin du lapin.
7. La maison de David n'est pas jaune.
8. Le poisson vit dans la maison jaune.

Qui a le poisson ? Codage : personnes 0 (Alice) à 3 (David) ; animaux 0 chat, 1 chien,
2 poisson, 3 lapin ; couleurs 0 rouge, 1 verte, 2 bleue, 3 jaune. `animal[i]` est l'animal de la
personne `i`, `couleur[i]` sa couleur.

## À faire
1. Écris `reponse` (les deux listes) et prouve `reponse_ok`.
2. `unique` : c'est la seule solution (`decide` essaie les 576 possibilités).""",
"""def Indices (animal couleur : List Nat) : Bool :=
  let a := animal.getD
  let c := couleur.getD
  a 0 0 != 0 && c 1 0 == 0 &&
  (List.range 4).all (fun i => a i 0 != 1 || c i 0 == 2) &&
  a 2 0 != 2 && a 2 0 != 0 && c 0 0 != 1 &&
  (List.range 4).all (fun i => a i 0 != 0 ||
    (List.range 4).any (fun j => a j 0 == 3 && (i + 1 == j || j + 1 == i))) &&
  c 3 0 != 3 &&
  (List.range 4).all (fun i => a i 0 != 2 || c i 0 == 3)

def permutations4 : List (List Nat) :=
  [0, 1, 2, 3].flatMap fun a => [0, 1, 2, 3].flatMap fun b => [0, 1, 2, 3].flatMap fun c =>
    [0, 1, 2, 3].filterMap fun d => if [a, b, c, d].eraseDups.length == 4 then some [a, b, c, d] else none

def reponse : List Nat × List Nat := -- @exo
  ([2, 0, 3, 1], [3, 0, 1, 2])

theorem reponse_ok : Indices reponse.1 reponse.2 = true := by -- @exo
  decide

theorem unique : ∀ a ∈ permutations4, ∀ c ∈ permutations4, Indices a c = true → (a, c) = reponse := by -- @exo
  decide +kernel""",
["Indices 2 et 5 : quelle couleur reste pour Alice ? Puis l'indice 8…", "`unique` : `decide +kernel` vérifie les 24 × 24 combinaisons."], "Logique.Bilan",
ressources=["[Énigme d'Einstein (Wikipédia)](https://fr.wikipedia.org/wiki/%C3%89nigme_d%27Einstein)"])

en("Timbres", "Les timbres de 3 et 5", 2, [RD],
"""Avec des timbres de 3 € et de 5 €, quels affranchissements peut-on faire exactement ?
1, 2, 4 et 7 sont impossibles, mais **tout** montant à partir de 8 est possible.
(En général, avec `a` et `b` premiers entre eux, le plus grand montant impossible est `ab − a − b`.)

## À prouver
1. `timbres : 8 ≤ n → ∃ a b, n = 3 * a + 5 * b`
2. `pas_sept : ¬ ∃ a b, 7 = 3 * a + 5 * b`""",
"""theorem timbres (n : Nat) (h : 8 ≤ n) : ∃ a b, n = 3 * a + 5 * b := by -- @exo
  have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases this with h3 | h3 | h3
  · exact ⟨n / 3, 0, by omega⟩
  · exact ⟨(n - 10) / 3, 2, by omega⟩
  · exact ⟨(n - 5) / 3, 1, by omega⟩

theorem pas_sept : ¬ ∃ a b, 7 = 3 * a + 5 * b := by -- @exo
  rintro ⟨a, b, h⟩
  omega""",
["Trois cas selon `n % 3`. Si `n % 3 = 1`, utilise deux timbres de 5 (`n − 10` est multiple de 3).", "Pour donner les témoins : `exact ⟨n / 3, 0, by omega⟩`."], "Enigmes.CentOiseaux",
ressources=["[Problème des pièces de monnaie de Frobenius (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_des_pi%C3%A8ces_de_monnaie)"])

en("McNuggets", "Le théorème des McNuggets", 3, [RD],
"""Les McNuggets étaient vendus par boîtes de 6, 9 et 20. Quel est le plus grand nombre de nuggets
qu'on ne peut **pas** commander exactement ? Réponse : **43**. Tout nombre à partir de 44 est
possible.

## Se le représenter
Si on sait faire 44, 45, 46, 47, 48 et 49 (six nombres consécutifs), on sait faire tous les
suivants en ajoutant des boîtes de 6.

## À prouver
1. `pas_43 : ¬ Commande 43`
2. `a_partir_de_44 : 44 ≤ n → Commande n`""",
"""def Commande (n : Nat) : Prop := ∃ a b c, n = 6 * a + 9 * b + 20 * c

theorem pas_43 : ¬ Commande 43 := by -- @exo
  rintro ⟨a, b, c, h⟩
  omega

theorem a_partir_de_44 : ∀ n, 44 ≤ n → Commande n := by -- @exo
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro h
    by_cases h' : 50 ≤ n
    · obtain ⟨a, b, c, e⟩ := ih (n - 6) (by omega) (by omega)
      exact ⟨a + 1, b, c, by omega⟩
    · have : n = 44 ∨ n = 45 ∨ n = 46 ∨ n = 47 ∨ n = 48 ∨ n = 49 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨1, 2, 1, rfl⟩
      · exact ⟨0, 5, 0, rfl⟩
      · exact ⟨1, 0, 2, rfl⟩
      · exact ⟨0, 3, 1, rfl⟩
      · exact ⟨8, 0, 0, rfl⟩
      · exact ⟨0, 1, 2, rfl⟩""",
["`pas_43` : `omega` explore tout seul.", "`a_partir_de_44` : récurrence forte (`induction n using Nat.strongRecOn`). Si `n ≥ 50`, utilise `n − 6` ; sinon, donne les six décompositions à la main (44 = 6 + 18 + 20…)."], "Enigmes.Timbres",
ressources=["[Nombre de McNugget (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Coin_problem#McNugget_numbers)"])

# --- Jeux
NJ = "Parcours.Jeux"
exo("Jeux", "Soustraction", "Le jeu de soustraction 1-3-4", 3, [RD],
"""Un tas de `n` jetons ; chacun son tour, on en retire 1, 3 ou 4. Celui qui ne peut plus jouer a
perdu. Qui gagne ? En calculant les premières positions, on voit apparaître un motif de période 7 :
les positions **perdantes** (pour celui qui doit jouer) sont celles où `n ≡ 0` ou `2 (mod 7)`.

Une position est gagnante s'il existe un coup qui mène à une position perdante.

## À prouver
`gagne134_spec : gagne134 n = true ↔ n % 7 ≠ 0 ∧ n % 7 ≠ 2`""",
"""def gagne134 (n : Nat) : Bool :=
  if h : n = 0 then false
  else !gagne134 (n - 1) || (3 ≤ n && !gagne134 (n - 3)) || (4 ≤ n && !gagne134 (n - 4))
termination_by n
decreasing_by all_goals omega

theorem gagne134_spec (n : Nat) : gagne134 n = true ↔ (n % 7 ≠ 0 ∧ n % 7 ≠ 2) := by -- @exo
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [gagne134]
    by_cases h0 : n = 0
    · simp [h0]
    · have i1 := ih (n - 1) (by omega)
      have i3 := ih (n - 3) (by omega)
      have i4 := ih (n - 4) (by omega)
      simp only [h0, ↓reduceDIte, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_true_eq]
      cases g1 : gagne134 (n - 1) <;> cases g3 : gagne134 (n - 3) <;>
        cases g4 : gagne134 (n - 4) <;> simp_all <;> omega""",
["Récurrence forte (`induction n using Nat.strongRecOn`), avec les hypothèses pour `n − 1`, `n − 3` et `n − 4`.", "Transforme les booléens en propositions (`Bool.or_eq_true`, `Bool.and_eq_true`…), puis distingue les valeurs de `gagne134 (n − 1)`, etc. (`cases g : …`), et `omega`."], NJ, requiert="Jeux.FortBoyard",
ressources=["[Jeu de soustraction (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Subtraction_game)"])

exo("Jeux", "DonnantDonnant", "Donnant-donnant", 2, [LP, RD],
"""Le **dilemme du prisonnier répété** : à chaque tour, deux joueurs choisissent de coopérer
(`true`) ou de trahir (`false`). Gains : 3 chacun si les deux coopèrent, 1 chacun si les deux
trahissent, et 5 pour le traître contre 0 pour la victime.

En 1980, Robert Axelrod organisa un tournoi de programmes. Le vainqueur fut le plus simple :
**donnant-donnant** (coopérer au premier tour, puis copier le dernier coup de l'adversaire).
Paradoxe : le méchant (qui trahit toujours) ne perd **aucun** duel… mais finit dernier du tournoi !

## À prouver (sur des parties de 10 tours)
1. `duel : partie donnant mechant 10 [] [] = (9, 14)`
2. `mechant_invaincu` : le méchant gagne ou fait match nul contre chacun.
3. `tournoi` : les scores totaux sont 90 (gentil), 88 (méchant), 99 (donnant), 99 (rancunier).""",
"""/-- Une stratégie décide selon les coups passés de l'adversaire (le plus récent en tête). -/
abbrev Strategie := List Bool → Bool

def gentil : Strategie := fun _ => true
def mechant : Strategie := fun _ => false
def donnant : Strategie := fun h => h.headD true
def rancunier : Strategie := fun h => h.all id

def gainPD : Bool → Bool → Nat
  | true, true => 3
  | true, false => 0
  | false, true => 5
  | false, false => 1

/-- Scores de `s` et `t` après `n` tours (`hs`, `ht` : coups déjà joués par chacun). -/
def partie (s t : Strategie) : Nat → List Bool → List Bool → Nat × Nat
  | 0, _, _ => (0, 0)
  | n + 1, hs, ht =>
    let a := s ht
    let b := t hs
    let r := partie s t n (a :: hs) (b :: ht)
    (gainPD a b + r.1, gainPD b a + r.2)

def joueurs : List Strategie := [gentil, mechant, donnant, rancunier]

def total (s : Strategie) : Nat := (joueurs.map fun t => (partie s t 10 [] []).1).sum

theorem duel : partie donnant mechant 10 [] [] = (9, 14) := by -- @exo
  decide

theorem mechant_invaincu : ∀ t ∈ joueurs, (partie mechant t 10 [] []).2 ≤ (partie mechant t 10 [] []).1 := by -- @exo
  decide

theorem tournoi : joueurs.map total = [90, 88, 99, 99] := by -- @exo
  decide""",
["Tout est calcul : `decide`.", "Essaie `#eval partie donnant rancunier 10 [] []` pour explorer."], NJ, requiert="Jeux.Nash",
ressources=["[Dilemme du prisonnier (Wikipédia)](https://fr.wikipedia.org/wiki/Dilemme_du_prisonnier)", "[The Evolution of Trust (jeu interactif)](https://ncase.me/trust/)"])

# --- Programmes : le jeu de la vie
exo("Programmes", "JeuDeLaVie", "Le jeu de la vie", 2, ["Solutions.Programmes.Definitions"],
"""Le **jeu de la vie** de John Conway (1970) : sur une grille infinie, chaque cellule est vivante
ou morte. À chaque génération, une cellule morte avec exactement 3 voisines vivantes naît ; une
cellule vivante avec 2 ou 3 voisines survit ; les autres meurent. De ces règles minuscules naissent
des comportements incroyables (le jeu de la vie peut même simuler un ordinateur !).

Les cellules vivantes sont une liste de coordonnées.

## À prouver
1. `bloc_stable` : le bloc 2 × 2 ne bouge pas.
2. `clignotant_periode` : le clignotant (3 cellules en ligne) revient après 2 générations, pas 1.
3. `planeur_avance` : après 4 générations, le **planeur** s'est déplacé d'une case en diagonale.""",
"""def voisinsVie (c : Nat × Nat) : List (Nat × Nat) :=
  [(c.1 - 1, c.2 - 1), (c.1 - 1, c.2), (c.1 - 1, c.2 + 1), (c.1, c.2 - 1), (c.1, c.2 + 1),
   (c.1 + 1, c.2 - 1), (c.1 + 1, c.2), (c.1 + 1, c.2 + 1)]

def nbVivantes (vie : List (Nat × Nat)) (c : Nat × Nat) : Nat :=
  ((voisinsVie c).filter (vie.contains ·)).length

def generation (vie : List (Nat × Nat)) : List (Nat × Nat) :=
  (vie ++ vie.flatMap voisinsVie).eraseDups.filter fun c =>
    nbVivantes vie c == 3 || (nbVivantes vie c == 2 && vie.contains c)

def memes (a b : List (Nat × Nat)) : Bool := a.all (b.contains ·) && b.all (a.contains ·)

def bloc : List (Nat × Nat) := [(2, 2), (2, 3), (3, 2), (3, 3)]
def clignotant : List (Nat × Nat) := [(3, 2), (3, 3), (3, 4)]
def planeur : List (Nat × Nat) := [(2, 3), (3, 4), (4, 2), (4, 3), (4, 4)]

theorem bloc_stable : memes (generation bloc) bloc = true := by -- @exo
  decide

theorem clignotant_periode : memes (repeter generation 2 clignotant) clignotant = true ∧
    memes (generation clignotant) clignotant = false := by -- @exo
  decide

theorem planeur_avance :
    memes (repeter generation 4 planeur) (planeur.map fun c => (c.1 + 1, c.2 + 1)) = true := by -- @exo
  decide +kernel""",
["Ce sont des simulations : `decide` (ou `decide +kernel`).", "Les coordonnées commencent à 2 pour éviter les soustractions tronquées de `Nat` au bord."], "Parcours.Prog", requiert="Programmes.Magicien",
ressources=["[Jeu de la vie (Wikipédia)](https://fr.wikipedia.org/wiki/Jeu_de_la_vie)", "[Simulateur en ligne (playgameoflife.com)](https://playgameoflife.com/)"])

ecrire_tout()
