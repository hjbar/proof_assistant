---
title: Rapport pour le _projet d'assistant de preuves_
author: Hugo BARREIRO
---

# Introduction

Ce projet a tout pour me plaire. On va s'attaquer à l'implémentation d'un assistant de preuves, un exercice que je n'ai jamais fait. On va traiter de logique, de typage et du lambda-calcul. Cerise sur le gâteau, on va tout coder en OCaml.

# Qu'est-ce qui a été implémenté dans le projet

## Les types simples

Toutes les questions non optionnelles ont été traitées. De plus, la question optionnelle de la partie 2.5, qui consiste à stocker les commandes de la preuve en cours dans un fichier, a été traitée. Néanmoins, la partie 4 optionnelle n'a pas été traitée.

## Les types dépendants

Aucune question ou partie optionnelle n'a été traitée. De plus, je n'ai pas fait toutes les preuves de la partie 5.14. Ainsi, il manque la preuve concernant la commutativité de l'addition, l'élément neutre de la multiplication des deux côtés, la commutativité de la multiplication et l'associativité de la multiplication. Elles n'ont pas été traitées par manque de temps. Le reste des questions et parties a été traité.

# Les difficultés encontrées

La première difficulté rencontrée a été le manque de temps. En effet, les TPs d'Agda, bien que très prenants, sont très longs. Ainsi, c'était compliqué de finir les TPs d'Agda et d'avancer sur le projet en même temps.

Ensuite, certaines instructions n'étaient pas très claires, notamment pour la partie sur les types dépendants. Par exemple, cela a pu être le cas pour l'implémentation de la fonction ```infer```.

De plus, le prouveur n'est pas très lisible pour la partie de types simples, ce qui complique les preuves. Néanmoins, il est quand même assez pratique comparé à celui des types dépendants. En effet, quand la preuve est grosse, il est compliqué de l'écrire car on ne dispose pas d'une interface détaillée avec le but, les variables, les types et les erreurs comme cela peut être le cas en Agda. Par exemple, on ne peut pas définir un gros terme en définissant d'abord de plus petits termes puisque des variables qui étaient sous des lambdas (et donc capturées) se retrouvent libres, et ainsi le terme devient mal typé et le prouveur bloque.

Enfin, la partie qui m'a demandé le plus d'effort est celle sur les types dépendants car elle est moins guidée que les autres. En plus d'exiger davantage de connaissances, elle comporte plus de subtilités dans l'implémentation. Il est également compliqué de bien tester que la substitution, la normalisation et l'inférence de type soient correctes.

# Les choix d'implémentations

Tout d'abord, j'ai décidé de remanier l'organisation du projet. En ce sens, j'ai réparti le code, pour le répertoire ```simple``` et le répertoire ```dependent```, dans des fichiers différents afin de séparer le code pour les tests unitaires, le ```main``` du prouveur et les fonctions permettant de le faire fonctionner.

Dans l'implémentation de la question optionnelle de la partie 2.5, j'ai choisi de sauvegarder uniquement les commandes correctes et de les stocker dans le fichier ```tmp/tmp.proof```.

Ensuite, pour la partie 3.2, j'ai fait le choix de mettre les règles ```zero``` et ```suc``` en dehors de la règle ```intro```. En effet, je trouvais ça plus simple, compréhensible et naturel.

J'ai fait le choix d'avoir partout un affichage ```UTF-8``` afin d'être cool. C'est pour cela que j'ai aussi choisi d'afficher les entiers naturels par des nombres décimaux à la place des ```zéro``` et des ```S S ... zéro```. Par exemple, ```zéro``` est affiché par ```0```, et ```S S Z``` par ```2```.

Enfin, j'ai codé une fonction ```has_fv``` qui indique si un lambda-terme possède des variables libres afin d'améliorer un peu l'efficacité de la substitution.

# Les extensions possibles

Tout d'abord, avec plus de temps j'aurais aimé effectuer toutes les preuves de la partie 5.14. De plus, j'aurais également apprécié faire toutes les questions et parties optionnelles.

Ensuite, concernant des extensions qui ne figurent pas sur le sujet, on pourrait imaginer implémenter toujours plus de constructions afin d'enrichir encore le langage et pourquoi pas se retrouver avec un petit langage ML.

De plus, on peut aussi penser à améliorer l'interactivité du prouveur, notamment pour les types dépendants, afin de rendre agréable son utilisation et de faciliter les preuves (bien que ce genre d'implémentation ne soit pas très pertinent concernant le but premier de ce projet).

On peut également penser à des optimisations diverses.

Une première serait par exemple de se passer de la substitution et normalisation classiques pour, à la place, utiliser une des variantes de la machine de Krivine, ce qui permet d'économiser des substitutions et d'éviter de recalculer tout un tas de termes.

Une autre, plus simple, pourrait être d'implémenter l'alpha-équivalence sans utiliser de substitution. Cela est possible notamment avec les ```Map``` OCaml, par exemple. Il suffit d'avoir un générateur de variables fraîches et d'associer chaque variable dans un lambda à une variable fraîche et d'aller chercher cette variable fraîche dans le cas des variables pour comparer les deux termes. Ainsi, on pourrait coder l'alpha-équivalence beaucoup plus efficacement. Cette extension devient évidemment obsolète si on décide de travailler avec la notation de De Bruijn.

Enfin, une dernière idée d'extension plutôt avancée pourrait être d'utiliser des GADTs à la place des ADTs. En effet, cela permettrait de se passer des multiples ```assert false``` un peu partout dans l'inférence de types, par exemple. On pourrait forcer à la création que le terme soit bien typé grâce aux propriétés des GADTs.

# Conclusion

Ce projet était très intéressant car il abordait notamment le lambda-calcul ou encore le typage, qui sont des concepts que j'apprécie tout particulièrement.

Coder est souvent un moyen de mieux comprendre des concepts théoriques. Cela a été encore le cas ici. Après avoir terminé le projet, j'ai beaucoup mieux compris le fonctionnement des types dépendants. De manière plus globale sur le cours, je trouve vraiment pédagogique et ludique d'aborder un concept théorique puis de l'implémenter.

Le projet complète les premiers TPs ainsi que ceux en Agda. En effet, on aborde l'inférence de types dépendants, ce que nous n'avions pas traité en TP. De plus, le prouveur des types simples ressemble davantage à Coq, notamment grâce à l'utilisation de tactiques, ce qui est complémentaire avec les TPs en Agda.
