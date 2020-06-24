# The Universe Level Issue

Dans cette Note, j'explique les problème que je rencontre en essayant de régler le problème de niveau d'univers dans la traduction Agda des fichier arith_fermat/*.dk.
Tous les message d'erreur n'y sont pas répertoriés, mais pour chaque "type" de problème j'ai fournis un exemple et des pistes pour le régler (ainsi que les limitations de ces pistes)

## Problèmes

### ForallK/P

Tout d'abord, mis a part le problème des niveaux d'univers sur Prop, la version de la PR ne prends pas en compte une information dans le papier : "Sharing a library between proof assistants reaching out to the HOL family" de Francois Thiré.
Dans la section 4 "From Dedukti[STTfa] to Coq and Matita" il est écrit : "Only three universes are needed for the translation: ~~the impredicative universe _Prop_ for Prop~~, _Type1_ for monotypes and _Type2_ for polytypes.".
Le problème étant que dans Coq, l'universe imprédicatif Prop habite entièrement dans Type1 (il est de type Type0). Or dans cette traduction vers Agda, Prop habite dans Set1, mais pas Prop1 (ni Prop (lsuc _) d'ailleurs). Donc les quantificateurs ForallP et ForallK posent problème.

Une solution serait d'utiliser le polymorphisme d'univers sur ces quantificateurs (ForallK/P) et leurs équivalents (ForallPI/AbsTy):  
`{^k : Level} (... : Set (lsuc ^k)) -> ...`  
Ou alors, une autre solution serait de laisser Agda trouver les niveaux (mais cela risque de résulter en plein de unresolved meta si utilisé un trop grand nombre de fois):  
`(... : Set _) -> ...`

Si l'on fait du polymorphisme d'univers, on se retrouve avec une erreur dans logic.agda (la même que le Problème 1.1)  
Si l'on mets ForallK polymorphique mais ForallP avec \_, on a des unresolved meta dans connectives.  
Si l'on mets \_ partout, on a plein de problèmes de meta.  
Dans tous les cas, leibniz ne type-check pas car on ne s'est toujours pas occupé des problèmes liés a Prop.  

### Prop

En fait, leibniz et connectives peuvent type-check seuls car c'est facile de le faire sans qu'ils ne soient utilisés dans d'autres fichiers. Mais dès qu'ils sont utilisés (dans logic ou dans bool par exemple pour rester simple) il y a des problème de niveau d'univers. Par exemple, `And : Set -> Set -> Set` suffit seul, mais si il est utilisé sur un Set1 dans un autre fichier, ca ne fonctionne plus et l'erreur proviendra de ce nouveau fichier qui donnera sûrement l'erreur : `Setn != Set` (avec n un entier strictement positif).  
Exemples :

- _primes.eq\_mod\_to\_divides_ contient des appels à logic.eq sur (nat.nat) mais aussi sur Prop  
- _relations.RC_ contient des appels à connectives.Or sur R, un fonction qui retourne Prop mais  
- _bool.agda_ contient des appels à connectives.Or sur bool : Set1  

Et on ne peut pas laisser un seul `Set0` car on ne peut pas savoir à l'avance "facilement" si cet argument de type `Set` sera utilisé comme un `Set (lsuc _)` plus tard. (une méthode pour deviner les niveaux serait de créer un type checker de niveau d'univers qui trouve et résout les contraintes pour à la fin assigner les niveaux)

Il faut donc les rendre génériques. Pour cela, on peut :

- utiliser le polymorphisme d'univers `And : {^1 ^2 ^3 : Level} -> Set ^1 -> Set ^2 -> Set ^3`
- laisser Agda deviner `And : Set _ -> Set _ -> Set _`
- utiliser l'option `--cumulativity` (Depuis la doc Agda : "`Nat : Set` For example, in addition to its usual type Set, Nat also has the type Set₁ and even Set i for any i : Level").

Le 1er point résulte en méta non-résolues dans connectives (comment l'expression `postulate I : True` peut elle deviner son niveau sachant que `True` est devenu `postulate True : {^1 : Level} -> Set ^1` ?)  
Le 2e point est facile à implémenter mais cause de nombreuses unresolved meta.  
Le 3e est très pratique car il permet de se "rapprocher" du fonctionnement de Type de Coq, de laisser Set à beaucoup d'endroits, et de laisser les ForallK et P sur Set1 (mais pas sûr, a prendre avec des pincettes). MAIS c'est une toute nouvelle feature qui n'est pas compatible avec le polymorphisme d'univers et qui n'a pas un bon solveur de niveau d'univers pour l'instant. De plus, cela ne fait que retarder le problème car si une fonction comme leibniz qui utilise le niveau j fonctionne sur tout i >= j, il reste le problème du type dans la déclaration qui est successeur de celui dans la définition, à résoudre (cf Problème 1).  

### Problème 1

Un des premiers problème rencontrés est que le type de retour de leibniz.leibniz dépends de la definition. En effet, on a :

```stderr
/home/alak/Documents/Code/Deducteam/MyVersion/Logipedia/export/agda/leibniz.agda:3,49-82
Set₁ != Set
when checking that the expression (P : A → Set) → P x → P y has
type Set
```

Pour régler ce Problème, on peut :  

- mettre `Set _` en type de retour (ou plus généralement, mettre `Set _` partout où il y a `Set0` dans les types)
- `Set1` (demande de calculer à la main le type alors que `Set _` s'en charge)
- utiliser le polymorphisme d'univers `leibniz : {^1 : Level} -> (A : Set2) -> A -> A -> Prop (lsuc i)\nleibniz {i} = . . . Prop i` (mais ici aussi, il faut savoir que Prop dans le type est 1 niveau au dessus que celui dans la définition)
- supprimer les types des fonctions et de ne laisser que les définitions __@goto_problème_2__ mais avec la solution pour ForallK/P consistant à utiliser `_` cause directement des unresolved meta car le type checker n'au aucun moyen de remplir les wildcards.

Plus généralement, dans la plupart des fonctions (Definition et Theorem dans sttfa), le niveau de `Set` doit être deviné de la définition.

### Problème 2

Plus de problème sur leibniz.agda ni connectives.agda, les 2 "feuilles" dans le graphe des dépendances de arith_fermat.

```stderr
/home/alak/Documents/Code/Deducteam/MyVersion/Logipedia/export/agda/logic.agda:7,117-152
Set₁ != Set
when checking that the expression (P : A → Set) → P :::: → P x has
type Set
```

Ce problème est causé car dans le fichier logic, l'axiom eq::ind et le théorème eq::rect::r sont défini de la sorte :  

```agda
postulate eq::ind : (A : _) -> (x : A) -> (P : (A -> Set)) -> (P x) -> (y : A) -> (eq (A) x y) -> P y
eq::rect::r : (A : _) -> (a : A) -> (x : A) -> (eq (A) x a) -> (P : (A -> Set)) -> (P a) -> P x
eq::rect::r = \(A : Set1) -> \(a : A) -> \(x : A) -> \(p : eq (A) x a) -> (((((((eq::ind) (A)) (x)) (\(:::: : A) -> (P : (A -> Set)) -> (P ::::) -> P x)) (\(P : A -> Set) -> \(auto : P x) -> (auto))) (a)) (p))
```

(ici ForallK et ForallP traduit avec `(A : _)` mais le problème persiste qu'importe la version de ForallK/P utilisée)  

Pour régler ce problème, on peut utiliser le polymorphisme d'univers sur `Set` dans `eq::ind` : `eq::ind : {^1 : Level} -> . . . -> (P : (A -> Set ^1)) -> . . .`  
Une autre méthode est de remplacer `Set` par `Set1` dans `eq::ind`. Mais ce n'est pas un fix global car par exemple, en utilisant la cumulativité, ce problème est déplacé vers `eq_coerc`.

Ceci résout tous les problème pour logic.agda. Mais un autre problème survient __@goto_problème_3__
Aussi, si on fait la même chose pour `eq`, il y a un problème de métas non résolues.

### Problème 3

```stderr
/home/alak/Documents/Code/Deducteam/MyVersion/Logipedia/export/agda/bool.agda:25,118-137
Set₁ != Set
when checking that the expression (P : Set) → P → P has type Set
```

bool.agda est un fichier difficile. Car même si il est facile de faire type-check leibniz, connectives, relations, et logic; bool a beaucoup plus de problèmes.
Commenter le type de ce théorem ne fait que décaler le problème dans la définition.
Ici, en changeant chaque `Set` par `Set _`, Il y a quand même le même problème au même endroit.
En fait, eq::ind utilisé juste avant restreint le type de retour de match::bool::type (qui dépends de son 1er argument). Donc le problème vient sûrement de eq::ind. (ou d'autres fonction qui type-check seule car elle ne fonctionne que sur 1 niveau et non tous)

Pour l'instant, aucune combinaison des méthodes proposé au long de cette Note n'ont aboutis à une résolution de cette erreur (a part commenter entièrement ce Théorem).

## Conclusion

Malheureusement, je n'ai pas encore trouvé de solution car soit il n'y a pas assez de contraintes (unresolved meta), soit les fichiers en sortie ne typent pas. MAIS il y a forcément une solution pour cette preuve car elle n'utilise pas l'imprédicativité (Testé via Coq en remplaçant Prop par Type).
