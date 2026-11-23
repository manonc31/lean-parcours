#!/usr/bin/env python3
"""Génère la branche Gymnase (petits exercices d'entraînement, un réflexe à la fois).
Outil de maintenance : écrit Solutions/Gymnase/*.lean. Relancer Outils/generer.py ensuite."""
import os

RACINE = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DOSSIER = os.path.join(RACINE, "Solutions", "Gymnase")

BASE = "ParcoursOutils"
NAT = "Solutions.Naturels.Transfert"
LISTES = "Solutions.Listes.Pont"
ANNEAU = "Solutions.Naturels.Carre"
LOGIQUE = "Solutions.Logique.Bilan"

E = []  # (id, titre, difficulte, imports, requiert, enonce, code, indices)


def ex(ident, titre, diff, imports, requiert, enonce, code, indices):
    E.append((ident, titre, diff, imports, requiert, enonce, code, indices))


# ---------------------------------------------------------------- égalités et rw
ex("Calcul", "Lean sait calculer", 1, [BASE], "Tutoriel.Bienvenue",
   "Quand les deux côtés d'une égalité se **calculent** en la même valeur, `rfl` suffit : "
   "Lean évalue `2 + 3` tout seul. (On peut aussi demander à Lean de calculer avec "
   "`#eval 2 + 3` : essaie !)",
   "theorem calcul : (2 : Nat) + 3 = 5 := by -- @exo\n  rfl\n\ntheorem calcul_bis : (7 : Nat) * 6 = 42 := by -- @exo\n  rfl",
   ["`rfl` dans les deux cas."])
ex("RwSimple", "Remplacer une variable", 1, [BASE], "Tutoriel.Reecrire",
   "`rw [h]` remplace `x` par `3` partout dans le but. Ensuite, `rw` essaie `rfl` tout seul.",
   "theorem rw_simple (x : Nat) (h : x = 3) : x + x = 6 := by -- @exo\n  rw [h]",
   ["`rw [h]` et c'est fini : après réécriture, le but `3 + 3 = 6` se calcule."])
ex("RwArriere", "Réécrire à l'envers", 1, [BASE], "Gymnase.RwSimple",
   "Ici `h : 4 = y` : on veut remplacer `y` par `4`, c'est-à-dire réécrire de **droite à gauche** : "
   "`rw [← h]` (la flèche se tape `\\l`).",
   "theorem rw_arriere (y : Nat) (h : 4 = y) : y + 1 = 5 := by -- @exo\n  rw [← h]",
   ["`rw [← h]`."])
ex("RwDansHyp", "Réécrire dans une hypothèse", 1, [BASE], "Gymnase.RwArriere",
   "`rw [h1] at h2` réécrit **dans l'hypothèse** `h2` au lieu du but. Puis `exact h2`.",
   "theorem rw_dans_hyp (a b : Nat) (h1 : a = b) (h2 : a + 1 = 7) : b + 1 = 7 := by -- @exo\n  rw [h1] at h2\n  exact h2",
   ["`rw [h1] at h2`, puis `exact h2`."])
ex("RwChaine", "Une chaîne de réécritures", 1, [BASE], "Gymnase.RwDansHyp",
   "`rw [h1, h2, h3]` enchaîne plusieurs réécritures. Regarde l'infoview entre chaque étape "
   "(place le curseur après chaque virgule).",
   "theorem rw_chaine (a b c : Nat) (h1 : a = b) (h2 : b = c) (h3 : c = 5) : a = 5 := by -- @exo\n  rw [h1, h2, h3]",
   ["`rw [h1, h2, h3]`."])
ex("Calc", "Raisonner par étapes avec calc", 2, [BASE], "Gymnase.RwChaine",
   "`calc` permet d'écrire une preuve comme au tableau :\n\n```\ncalc a = b + 1 := h1\n  _ = 2 + 1 := by rw [h2]\n  _ = 3 := rfl\n```\n"
   "Chaque ligne `_ = …` continue la chaîne, avec sa justification après `:=`.",
   "theorem calc_exemple (a b : Nat) (h1 : a = b + 1) (h2 : b = 2) : a = 3 := by -- @exo\n  calc a = b + 1 := h1\n    _ = 2 + 1 := by rw [h2]\n    _ = 3 := rfl",
   ["Recopie la structure de l'énoncé.", "Pas besoin de `calc` en fait : `rw [h1, h2]` marche aussi !"])
# ---------------------------------------------------------------- implication
ex("Intro", "Introduire des hypothèses", 1, [BASE], "Tutoriel.Hypotheses",
   "Pour prouver `P → Q → P`, `intro hp hq` introduit les deux hypothèses ; il reste à prouver `P`.",
   "theorem intro_exemple (P Q : Prop) : P → Q → P := by -- @exo\n  intro hp _\n  exact hp",
   ["`intro hp hq` puis `exact hp`."])
ex("Echange", "Échanger les hypothèses", 1, [BASE], "Gymnase.Intro",
   "Une fonction de deux arguments peut prendre ses arguments dans l'autre ordre.",
   "theorem echange (P Q R : Prop) : (P → Q → R) → (Q → P → R) := by -- @exo\n  intro h hq hp\n  exact h hp hq",
   ["`intro h hq hp`, puis `exact h hp hq`."])
ex("Apply", "Raisonner à rebours avec apply", 1, [BASE], "Gymnase.Intro",
   "`apply hqr` : « pour prouver `R`, il suffit de prouver `Q` ». Le but devient `Q`.",
   "theorem apply_exemple (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) (hp : P) : R := by -- @exo\n  apply hqr\n  apply hpq\n  exact hp",
   ["`apply hqr`, `apply hpq`, `exact hp`."])
ex("Have", "Étapes intermédiaires avec have", 1, [BASE], "Gymnase.Apply",
   "`have hq : Q := hpq hp` ajoute un nouveau fait à tes hypothèses. Pratique pour découper une preuve.",
   "theorem have_exemple (P Q R : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) : R := by -- @exo\n  have hq : Q := hpq hp\n  have hr : R := hqr hq\n  exact hr",
   ["`have hq : Q := hpq hp`."])
ex("PourTout", "Utiliser un « pour tout »", 1, [BASE], "Gymnase.Have",
   "`h : ∀ n, P n` s'applique à n'importe quel `n` : `h 5 : P 5`. Variante : `specialize h 5` remplace `h` par `h 5`.",
   "theorem pour_tout_exemple (P : Nat → Prop) (h : ∀ n, P n) : P 5 := by -- @exo\n  exact h 5\n\ntheorem pour_tout_intro : ∀ n : Nat, n = n := by -- @exo\n  intro n\n  rfl",
   ["`exact h 5`.", "Pour le second : `intro n` puis `rfl`."])
# ---------------------------------------------------------------- et / ou / iff
ex("Constructor", "Construire un « et »", 1, [BASE], "Logique.Et",
   "`constructor` découpe le but `A ∧ B` en deux buts `A` et `B`. Traite-les avec `·` (tapé `\\.`).",
   "theorem constructor_exemple (P Q : Prop) (hp : P) (hq : Q) : Q ∧ P := by -- @exo\n  constructor\n  · exact hq\n  · exact hp",
   ["`constructor`, puis `· exact hq` et `· exact hp`."])
ex("Obtain", "Découper un « et » triple", 1, [BASE], "Gymnase.Constructor",
   "`P ∧ Q ∧ R` se lit `P ∧ (Q ∧ R)`. `obtain ⟨hp, hq, hr⟩ := h` découpe tout d'un coup.",
   "theorem obtain_exemple (P Q R : Prop) (h : P ∧ Q ∧ R) : R := by -- @exo\n  obtain ⟨_, _, hr⟩ := h\n  exact hr",
   ["`obtain ⟨hp, hq, hr⟩ := h`."])
ex("Gauche", "Choisir un côté", 1, [BASE], "Logique.Ou",
   "Pour prouver `P ∨ (Q ∨ R)` à partir de `Q` : `right` puis `left`.",
   "theorem gauche_droite (P Q R : Prop) (hq : Q) : P ∨ Q ∨ R := by -- @exo\n  right\n  left\n  exact hq",
   ["`right`, `left`, `exact hq`."])
ex("Rcases", "Raisonner par cas", 1, [BASE], "Gymnase.Gauche",
   "`rcases h with hp | hq` crée deux buts : un où `P` est vrai, un où `Q` est vrai.",
   "theorem rcases_exemple (P Q R : Prop) (h : P ∨ Q) (hpr : P → R) (hqr : Q → R) : R := by -- @exo\n  rcases h with hp | hq\n  · exact hpr hp\n  · exact hqr hq",
   ["`rcases h with hp | hq` puis deux `exact`."])
ex("RwIff", "Réécrire avec une équivalence", 2, [BASE], "Logique.Equivalence",
   "`rw` marche aussi avec `h : P ↔ Q` : il remplace la **proposition** `P` par `Q` dans le but.",
   "theorem rw_iff (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by -- @exo\n  rw [h]\n  exact hq",
   ["`rw [h]` puis `exact hq`."])
# ---------------------------------------------------------------- existe
ex("Temoin", "Donner un témoin", 1, [BASE], "Logique.Existe",
   "Pour prouver `∃ n, n + 2 = 5`, il suffit de donner `n` : `exact ⟨3, rfl⟩` (le témoin, puis la preuve).",
   "theorem temoin : ∃ n : Nat, n + 2 = 5 := by -- @exo\n  exact ⟨3, rfl⟩\n\ntheorem temoin_double : ∃ a b : Nat, a + b = 10 ∧ a = 2 * b + 1 := by -- @exo\n  exact ⟨7, 3, rfl, rfl⟩",
   ["`exact ⟨3, rfl⟩`.", "Pour le second, cherche `a` et `b` de tête, puis `exact ⟨a, b, rfl, rfl⟩`."])
ex("Transfert", "Transporter un « il existe »", 1, [BASE], "Gymnase.Temoin",
   "On récupère le témoin d'une hypothèse (`obtain ⟨n, hn⟩ := h`), et on le réutilise.",
   "theorem transport (f g : Nat → Nat) (h : ∃ n, f n = 0) (hfg : ∀ n, f n = 0 → g n = 1) :\n    ∃ n, g n = 1 := by -- @exo\n  obtain ⟨n, hn⟩ := h\n  exact ⟨n, hfg n hn⟩",
   ["`obtain ⟨n, hn⟩ := h`, puis `exact ⟨n, hfg n hn⟩`."])
# ---------------------------------------------------------------- absurde
ex("Exfalso", "Du faux, on déduit n'importe quoi", 1, [BASE], "Logique.Negation",
   "Si tu as `h : False`, `exfalso` remplace le but par `False`, puis `exact h`. "
   "(Ou directement `exact h.elim`.)",
   "theorem exfalso_exemple (h : False) : (2 : Nat) + 2 = 5 := by -- @exo\n  exfalso\n  exact h",
   ["`exfalso` puis `exact h`."])
ex("Contradiction", "Repérer une contradiction", 1, [BASE], "Gymnase.Exfalso",
   "Avec `hp : P` et `hnp : ¬P`, la tactique `contradiction` conclut toute seule. "
   "Elle repère aussi les égalités impossibles entre constructeurs, comme `0 = n + 1`.",
   "theorem contradiction_exemple (P Q : Prop) (hp : P) (hnp : ¬P) : Q := by -- @exo\n  contradiction\n\ntheorem pas_de_predecesseur (n : Nat) (h : n + 1 = 0) : False := by -- @exo\n  contradiction",
   ["`contradiction` dans les deux cas."])
ex("Decide", "Faire vérifier par la machine", 1, [BASE], "Gymnase.Contradiction",
   "Pour un énoncé **sans variable** qui se vérifie par calcul (égalités, inégalités, `≠` sur des nombres…), "
   "`decide` fait le calcul et conclut.",
   "theorem decide_ne : (2 : Nat) ≠ 3 := by -- @exo\n  decide\n\ntheorem decide_reste : (17 : Nat) % 5 = 2 := by -- @exo\n  decide\n\ntheorem decide_ou : (10 : Nat) < 3 ∨ 2 ≤ 2 := by -- @exo\n  decide",
   ["`decide` à chaque fois."])
ex("ParCas", "by_cases : vrai ou faux ?", 2, [BASE], "Logique.Classique",
   "`by_cases h : P` crée deux cas : un avec `h : P`, l'autre avec `h : ¬P`. (Logique classique.)",
   "theorem par_cas (P Q : Prop) (h1 : P → Q) (h2 : ¬P → Q) : Q := by -- @exo\n  by_cases h : P\n  · exact h1 h\n  · exact h2 h",
   ["`by_cases h : P`."])
# ---------------------------------------------------------------- fonctions et booléens
ex("Funext", "Deux fonctions égales", 2, [BASE], "Logique.Egalite",
   "Deux fonctions sont égales si elles donnent le même résultat partout : `funext x` "
   "transforme le but `f = g` en `f x = g x`.",
   "theorem funext_exemple (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by -- @exo\n  funext x\n  exact h x\n\ntheorem composee : (fun x : Nat => x + 1) ∘ (fun x => 2 * x) = fun x => 2 * x + 1 := by -- @exo\n  funext x\n  rfl",
   ["`funext x` puis `exact h x`.", "Pour la composée, après `funext x`, c'est vrai par calcul (`rfl`)."])
ex("Booleens", "Raisonner sur les booléens", 1, [BASE], "Gymnase.Decide",
   "Un booléen est `true` ou `false`. `cases b` examine les deux cas ; dans chacun, `rfl` calcule. "
   "Raccourci : `cases b <;> rfl` applique `rfl` à tous les cas.",
   "theorem et_vrai (b : Bool) : (b && true) = b := by -- @exo\n  cases b <;> rfl\n\ntheorem non_non (b : Bool) : (!(!b)) = b := by -- @exo\n  cases b <;> rfl\n\ntheorem ou_comm_bool (a b : Bool) : (a || b) = (b || a) := by -- @exo\n  cases a <;> cases b <;> rfl",
   ["`cases b <;> rfl`.", "Pour deux booléens : `cases a <;> cases b <;> rfl`."])
# ---------------------------------------------------------------- après le Pont (omega, simp)
ex("Omega", "La tactique omega", 1, [NAT], "Naturels.Transfert",
   "Depuis le Pont des entiers, la tactique **`omega`** est débloquée : elle résout toute seule les "
   "problèmes d'arithmétique **linéaire** (+, −, ≤, <, multiplication par une constante) sur `Nat` et `Int`.",
   "theorem omega1 (a b : Nat) (h : a < b) : a + 1 ≤ b := by -- @exo\n  omega\n\ntheorem omega2 (x y : Nat) (h1 : x + y = 10) (h2 : x = y + 2) : x = 6 := by -- @exo\n  omega",
   ["`omega`."])
ex("OmegaLimites", "Les limites d'omega", 2, [NAT], "Gymnase.Omega",
   "`omega` ne comprend pas la multiplication de deux **variables** (`a * b`) : il la traite comme une boîte noire. "
   "Ici, il faut d'abord établir un fait sur `a * b` avec un lemme (`Nat.mul_le_mul`), puis laisser `omega` finir.",
   "theorem omega_limite (a b : Nat) (ha : 2 ≤ a) (hb : 3 ≤ b) : 6 ≤ a * b + 0 := by -- @exo\n  have h : 2 * 3 ≤ a * b := Nat.mul_le_mul ha hb\n  omega",
   ["`have h : 2 * 3 ≤ a * b := Nat.mul_le_mul ha hb`, puis `omega`."])
ex("RecurrenceNat", "Une récurrence sur Nat", 2, [NAT], "Gymnase.Omega",
   "On définit `double n` par récurrence (`double 0 = 0`, `double (n+1) = double n + 2`). "
   "Prouve que `double n = 2 * n` : `induction n with`, puis dans le cas `succ`, déplie la définition "
   "(`rw [double]` ou `simp only [double]`) et utilise `ih` et `omega`.",
   "def double : Nat → Nat\n  | 0 => 0\n  | n + 1 => double n + 2\n\ntheorem double_eq (n : Nat) : double n = 2 * n := by -- @exo\n  induction n with\n  | zero => rfl\n  | succ n ih =>\n    rw [double, ih]\n    omega",
   ["`induction n with | zero => rfl | succ n ih => …`.", "Cas `succ` : `rw [double, ih]` puis `omega`."])
ex("Simp", "La tactique simp", 2, [LISTES], "Listes.Pont",
   "`simp` applique automatiquement des centaines de lemmes de simplification (`x + 0 = x`, "
   "`l ++ [] = l`, `(l₁ ++ l₂).length = …`…). Depuis les Ponts, ces lemmes sont débloqués. "
   "`simp [h]` ajoute une hypothèse `h` aux règles utilisées.",
   "theorem simp1 (l : List Nat) : (l ++ []).length = l.length := by -- @exo\n  simp\n\ntheorem simp2 (l₁ l₂ : List Nat) (h : l₁.length = 3) : (l₁ ++ l₂).length = 3 + l₂.length := by -- @exo\n  simp [h]",
   ["`simp`.", "`simp [h]`."])
ex("Grind", "La tactique grind", 2, [ANNEAU, LOGIQUE, NAT], "Naturels.Carre",
   "Depuis l'identité remarquable, **`grind`** est débloqué. C'est un « couteau suisse » : il "
   "combine calcul algébrique (anneaux), arithmétique linéaire, et raisonnement sur les égalités.",
   "theorem grind1 (a b : Nat) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by -- @exo\n  grind\n\ntheorem grind2 (x y : Int) (h : x = y + 1) : x * x - y * y = 2 * y + 1 := by -- @exo\n  subst h\n  grind",
   ["`grind`.", "Pour le second : `subst h` remplace `x` par `y + 1`, puis `grind`."])
ex("FunInduction", "La récurrence fonctionnelle", 3, [NAT], "Gymnase.RecurrenceNat",
   "Pour une fonction récursive qui ne suit pas un schéma simple, `fun_induction f n with` "
   "fait une récurrence qui **suit les appels récursifs** de `f`. Ici `pas2` descend de 2 en 2.",
   "def pas2 : Nat → Nat\n  | 0 => 0\n  | 1 => 1\n  | n + 2 => pas2 n + 2\n\ntheorem pas2_eq (n : Nat) : pas2 n = n := by -- @exo\n  fun_induction pas2 n with\n  | case1 => rfl\n  | case2 => rfl\n  | case3 n ih => omega",
   ["`fun_induction pas2 n with`, trois cas : `case1`, `case2`, `case3 n ih`.", "Dans le dernier cas, le but est `pas2 n + 2 = n + 2` : `omega` avec `ih`."])

# ---------------------------------------------------------------- deuxième série
ex("Symm", "Retourner une égalité", 1, [BASE], "Gymnase.RwSimple",
   "Si `h : 3 = x`, alors `h.symm : x = 3`. Le point permet d'appeler une fonction associée au type "
   "de `h` (ici `Eq.symm`) : c'est la **notation pointée**.",
   "theorem symm_exemple (x : Nat) (h : 3 = x) : x = 3 := by -- @exo\n  exact h.symm\n\ntheorem trans_exemple (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by -- @exo\n  exact h1.trans h2",
   ["`exact h.symm`.", "Pour le second : `exact h1.trans h2` (ou `rw [h1, h2]`)."])
ex("Congr", "Appliquer une fonction aux deux côtés", 1, [BASE], "Gymnase.Symm",
   "Si `a = b`, alors `f a = f b` : c'est `congrArg f h`. Ici la fonction est `fun x => x * 2`.",
   "theorem congr_exemple (a b : Nat) (h : a = b) : a * 2 = b * 2 := by -- @exo\n  exact congrArg (fun x => x * 2) h",
   ["`exact congrArg (fun x => x * 2) h`, ou plus simplement `rw [h]`."])
ex("Anonymes", "Les fonctions anonymes", 1, [BASE], "Gymnase.Calcul",
   "`fun x => x + 1` est la fonction qui à `x` associe `x + 1` (on peut aussi écrire `(· + 1)`). "
   "L'appliquer, c'est **remplacer** `x` : Lean le fait par calcul.",
   "theorem anonyme : (fun x : Nat => x + 1) 2 = 3 := by -- @exo\n  rfl\n\ntheorem eta (f : Nat → Nat) : (fun x => f x) = f := by -- @exo\n  rfl",
   ["`rfl` dans les deux cas : Lean simplifie `(fun x => …) a` tout seul (β-réduction)."])
ex("Motifs", "Introduire avec un motif", 1, [BASE], "Gymnase.Transfert",
   "`rintro ⟨x, hp, hq⟩` introduit une hypothèse `∃ x, P x ∧ Q x` et la découpe d'un coup.",
   "theorem motif (P Q : Nat → Prop) : (∃ x, P x ∧ Q x) → ∃ x, Q x := by -- @exo\n  rintro ⟨x, _, hq⟩\n  exact ⟨x, hq⟩",
   ["`rintro ⟨x, hp, hq⟩` puis `exact ⟨x, hq⟩`."])
ex("ImbriquesIntro", "Plusieurs quantificateurs", 1, [BASE], "Gymnase.PourTout",
   "`intro a b h` introduit d'un coup tous les `∀` et les hypothèses.",
   "theorem imbriques : ∀ a b : Nat, a = b → b = a := by -- @exo\n  intro a b h\n  exact h.symm",
   ["`intro a b h` puis `exact h.symm`."])
ex("Option", "Les valeurs optionnelles", 2, [BASE], "Gymnase.Booleens",
   "Une valeur `o : Option Nat` est soit `none` (rien), soit `some x`. Raisonne par cas avec `cases o`.",
   "theorem option_exemple (o : Option Nat) (h : o ≠ none) : ∃ x, o = some x := by -- @exo\n  cases o with\n  | none => exact absurd rfl h\n  | some x => exact ⟨x, rfl⟩",
   ["`cases o with | none => … | some x => …`.", "Cas `none` : `h : none ≠ none`, absurde (`absurd rfl h`)."])
ex("DecideFini", "Décider sur un ensemble fini", 1, [BASE], "Gymnase.Decide",
   "`Fin n` est le type des entiers `< n`. Un énoncé `∀ x : Fin 4, …` n'a que 4 cas : `decide` les vérifie tous.",
   "theorem fini1 : ∀ x : Fin 4, x.val * x.val < 10 := by -- @exo\n  decide\n\ntheorem fini2 : (List.range 5).foldl (· + ·) 0 = 10 := by -- @exo\n  decide",
   ["`decide`."])
ex("Subst", "Remplacer une variable partout", 2, [NAT], "Gymnase.Omega",
   "`subst h` (avec `h : x = 5`) remplace `x` par `5` **partout** (but et hypothèses), et fait disparaître `x`.",
   "theorem subst_exemple (x y : Nat) (h : x = 5) (h2 : x + y = 7) : y = 2 := by -- @exo\n  subst h\n  omega",
   ["`subst h`, puis `omega`."])
ex("ObtainRfl", "Déstructurer avec rfl", 2, [NAT], "Gymnase.Subst",
   "Dans `obtain ⟨k, rfl⟩ := h` (avec `h : ∃ k, n = 2 * k`), le motif `rfl` remplace directement `n` par `2 * k`.",
   "theorem pair_plus_pair (n : Nat) (h : ∃ k, n = 2 * k) : ∃ m, n + n = 4 * m := by -- @exo\n  obtain ⟨k, rfl⟩ := h\n  exact ⟨k, by omega⟩",
   ["`obtain ⟨k, rfl⟩ := h`, puis `exact ⟨k, by omega⟩`."])
ex("Equivalence", "Prouver une équivalence", 2, [NAT], "Gymnase.Omega",
   "Pour `P ↔ Q` : `constructor`, puis les deux sens.",
   "theorem equivalence_exemple (n : Nat) : n = 0 ↔ n + 1 = 1 := by -- @exo\n  constructor\n  · intro h\n    rw [h]\n  · intro h\n    omega",
   ["`constructor`, puis `intro h` dans chaque sens.", "Sens `→` : `rw [h]`. Sens `←` : `omega`."])
ex("Chercher", "Chercher un lemme avec exact?", 1, [NAT], "Gymnase.Omega",
   "`exact?` **cherche** dans la bibliothèque un lemme qui prouve le but, et te propose la ligne à écrire "
   "(clique dessus dans l'infoview). Ici, après le Pont, les lemmes de `Nat` sont permis.",
   "theorem chercher (a b : Nat) : a * b = b * a := by -- @exo\n  exact Nat.mul_comm a b",
   ["Écris `exact?` et regarde la suggestion dans l'infoview.", "Il trouve `Nat.mul_comm a b`."])
ex("CalcInegalites", "calc avec des inégalités", 2, [NAT], "Gymnase.Calc",
   "`calc` marche aussi avec `≤` et `<` : chaque étape peut être `=`, `≤` ou `<`, et Lean combine.",
   "theorem calc_ineg (a b c : Nat) (h1 : a ≤ b) (h2 : b < c) : a + 1 < c + 1 := by -- @exo\n  calc a + 1 ≤ b + 1 := by omega\n    _ < c + 1 := by omega",
   ["`calc a + 1 ≤ b + 1 := by omega` puis `_ < c + 1 := by omega`.", "Ou directement `omega` !"])
ex("ListesInduction", "Récurrence sur une liste", 2, [LISTES], "Gymnase.Simp",
   "`induction l with | nil => … | cons x l ih => …` : le cas de la liste vide, et le cas « un élément "
   "devant une liste pour laquelle c'est vrai ».",
   "theorem map_id' (l : List Nat) : l.map (fun x => x) = l := by -- @exo\n  induction l with\n  | nil => rfl\n  | cons x l ih => simp [ih]",
   ["`induction l with`.", "Cas `cons` : `simp [ih]`."])
ex("Deplier", "Déplier une définition", 2, [ANNEAU, LOGIQUE, NAT], "Gymnase.Grind",
   "`unfold carre` remplace `carre` par sa définition dans le but. Utile quand `rw` ou `simp` ne voient "
   "pas à travers une définition.",
   "def carre (n : Nat) : Nat := n * n\n\ntheorem carre_trois : carre 3 = 9 := by -- @exo\n  unfold carre\n  rfl\n\ntheorem carre_succ (n : Nat) : carre (n + 1) = carre n + 2 * n + 1 := by -- @exo\n  unfold carre\n  grind",
   ["`unfold carre` puis `rfl`.", "Pour le second : `unfold carre` puis `grind`."])
ex("Absurde", "Une égalité absurde", 1, [BASE], "Gymnase.Contradiction",
   "`2 = 3` est faux, et `decide` le sait : `(by decide : (2 : Nat) ≠ 3)`. Avec `absurd h preuve_de_non_h`, on conclut n'importe quoi.",
   "theorem absurde (h : (2 : Nat) = 3) : False := by -- @exo\n  exact absurd h (by decide)",
   ["`exact absurd h (by decide)`."])
ex("Tactiques", "Enchaîner les tactiques", 2, [BASE], "Gymnase.Rcases",
   "`t1 <;> t2` applique `t2` à **tous** les buts créés par `t1`. Pratique quand plusieurs cas se "
   "prouvent de la même façon.",
   "theorem enchainer (P Q : Prop) (hp : P) (hq : Q) : (P ∧ Q) ∧ (Q ∧ P) := by -- @exo\n  constructor <;> constructor <;> assumption",
   ["`constructor <;> constructor <;> assumption` (`assumption` cherche une hypothèse qui convient)."])


def ecrire():
    os.makedirs(DOSSIER, exist_ok=True)
    for (ident, titre, diff, imports, requiert, enonce, code, indices) in E:
        lignes = ["/- @parcours", f"titre: {titre}", f"difficulte: {diff}"]
        if requiert:
            lignes.append(f"requiert: {requiert}")
        for i in indices:
            lignes.append(f"indice: {i}")
        lignes.append("-/")
        for imp in imports:
            lignes.append(f"import {imp}")
        lignes.append("")
        lignes.append("/-!")
        lignes.append(f"# {titre}")
        lignes.append("")
        lignes.append(enonce)
        lignes.append("")
        lignes.append("Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.")
        lignes.append("-/")
        lignes.append("")
        lignes.append("namespace Parcours.Gymnase")
        lignes.append("")
        lignes.append(code)
        lignes.append("")
        lignes.append("end Parcours.Gymnase")
        lignes.append("")
        lignes.append("#verifier")
        with open(os.path.join(DOSSIER, ident + ".lean"), "w", encoding="utf-8") as f:
            f.write("\n".join(lignes) + "\n")
    print(len(E), "exercices du Gymnase écrits.")


if __name__ == "__main__":
    ecrire()
