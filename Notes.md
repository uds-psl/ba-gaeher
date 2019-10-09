Technische Probleme: 

* Weiterhin Probleme mit den notwendigen Instanzdeklarationen für setoid_rewrite - siehe Complexity/minimal.v

* Kann man solverec einfach erweitern (Hint Database / SMPL / o.ä.) ?
  - Konkret um Möglichkeiten, mit Monotonizität umzugehen, sowie mit Add Commutativity in Funktionsargumenten

* Best Practices, um neue Prelim-Sachen hinzuzufügen (am besten ohne dabei alles neu kompilieren zu müssen)

* Irgendwelche externen Bibliotheken mit mehr arithmetischen Facts? z.B. zu Division - Monotonie in Argumenten, etc.
* Rewrite-Instanzen mit Preconditions - z.B. bei Division in Argumenten mit Ungleichungen rewriten, aber unter der Voraussetzung, dass der Divisor > 0 ist

* Manchmal klappt das Inferieren der Registered-Instanz nicht -siehe z.B. makeEdgesLiteral_time_bound 

TODOs: 
* uniformes Format für die polybounds lemmas


Technische Wunschliste: 

* Taktiken bauen, die die Polynomialzeit-Beweise verkürzen

Inhaltliche Wunschliste: 
* eventuell NP hardness von 3SAT, SubsetSum, Hamiltonian Cycle, IP

* Cook's Theorem 

* Space formalisieren

* Space Hierarchy

* Savitch
  * dafür evtl andere Charakterisierung von Nichtdeterminismus

* coNP, logspace - vermutlich eher nicht



Remarks regarding the 3SAT to Clique reduction: 

* Reduction is formalised via a relation between CNFs and graphs. The graph is determined uniquely up to isomorphism, i.e. a function that labels its nodes. This labelling function connects the graph's nodes to parts of the CNF and thus formalises the idea of gadgets.

One possibility: 

* Graphs in the relation are abstract propositional graphs that cannot be extracted to L. I hope that it is easier to reason about this abstract model.

* The reduction function uses another simpler and weakly structured representation of graphs that is extractable to L. 

* For correctness, the graph output by the reduction is lifted to its corresponding abstract representation (up to isomorphism) and a suitable labelling function needs to be given.


What I do: 

* Relation works directly on the flat graphs. The overhead of the above approach would be huge.