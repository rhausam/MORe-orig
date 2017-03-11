# MORe-orig
Updated version of the original MORe OWL reasoner code.  This includes updates to OWL API 4.2.6 the Protege plugin to be compatible with Protege 5.1.0.  The JFact OWL 2 reasoner was replaced with FaCT++ 1.6.5 and the ELK reasoner was updated to version 0.4.3.  The HermiT reasoner used is version 1.3.8.413 (compatible with OWL API 4). 

**Original description and source code**

The original source code archive (on Google Code) can be found here:

https://code.google.com/archive/p/more-reasoner/

The original project description and acknowledgements are:

MORe: Modular Combination of OWL Reasoners for Ontology Classification

MORe Reasoner

MORe is a reasoner for TBox classification and named class satisfiability of ontologies written in the ontology language OWL 2 (see supported methods).

MORe is still under active development. The current distribution of MORe (v.0.1.5) integrates HermiT and JFact, as fully-fledged OWL 2 reasoners, with ELK (a reasoner for the OWL 2 EL profile) in a modular way. In particular, MORe exploits module extraction techniques to identify a subset of the ontology that can be completely classified using ELK.

MORe is designed in such a way that the fully-fledged (and slower) reasoner (i.e., HermiT or JFact) performs as few computations as possible, and the bulk of the computation is delegated to the more efficient, profile specific, ELK reasoner.

MORe, with the standalone distribution, can be used from the command line or integrated in other OWL API based applications. Additionally, MORe is also distributed as a Protege plugin.

Snow Owl also includes MORe as a reasoner option.

MORe is open-source and released under GNU Lesser GPL.

Awards

MORe has been awarded, in the OWL Reasoning Evaluation Workshop (ORE 2013), as the most robust reasoner for the class satisfiability of OWL 2 RL ontologies and as the best newcomer OWL reasoner. Additionally it has been one of the top-3 reasoners for the classification and class satisfiability of OWL 2 (DL) and OWL 2 EL ontologies.

Main Publications

Ana Armas Romero, Bernardo Cuenca Grau, and Ian Horrocks. MORe: Modular Combination of OWL Reasoners for Ontology Classification. In Proceedings of the 11th International Semantic Web Conference (ISWC 2012). Springer. 2012. Download (PDF)

Ana Armas Romero, Bernardo Cuenca Grau, and Ian Horrocks. Modular Combination of Reasoners for Ontology Classification. In Proc. of the 2012 Description Logic Workshop (DL 2012), volume 846 of CEUR (http://ceur-ws.org/), 2012. Download (PDF)

Ana Armas, Bernardo Cuenca Grau, Ian Horrocks and Ernesto Jimenez-Ruiz. MORe: a Modular OWL Reasoner for Ontology Classification. In OWL Reasoning Evaluation Workshop (ORE) 2013. Download (PDF)

Authors

MORe is currently developed by Ana Armas, Bernardo Cuenca Grau and Ian Horrocks. Ernesto Jimenez-Ruiz is also contributing to the project.

You are welcome to contact them via e-mail (see above links to homepages for addresses). You can also post questions, suggestions and issues to the discussion forum.

Acknowledgements

MORe is being developed in the Knowledge Representation and Reasoning group at the Department of Computer Science of the University of Oxford. This work was supported by the Royal Society, the Seventh Framework Program (FP7) of the European Commission under Grant Agreement 318338, "Optique", and the EPSRC projects ExODA, Score! and MaSI^3.
