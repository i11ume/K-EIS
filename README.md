# K-EIS

## Methods

In our experiments, all the code implements with C++ code.

### Our Methods 

Link: SourceCode/OurMethods

* 1-EIS: K-EIS for single target.
* K-EIS: K-EIS for multiple target.
* Mix-EIS: Improved K-EIS for multiple target based on subgraph partition.
* Mix-EIS-IGS: Mix-EIS includes a single-target searching algorithm, using IGS to replace 1-EIS for comparison.

### Compare Methods 

Link: SourceCode/CompareMethods

* IGS: A single-target search method over DAGs.
* TS-IGS: Improved IGS.
* BinG: A single-target search method over Tree.
* KBM-IGS1: A single-target search method over Tree.
* KBM-IGS2: A multiple-targets search method over Tree.

## Datasets&EXP

### Five Datasets

Link: Datasets&EXP

* ProductClassification: Tree.

* Amazon: Tree.
* ACM_CCS: DAG.
* Wiki_Edits: DAG.
* ImageNet: DAG.

Format:
The first line with two integer $n$, $m$ , represent the number of vertices and directed edges in the graph.

The next $m$ lines, each line contains two integer $u_i,v_i$, represent the $i$-th edge from $u_i$  to $v_i$ .

### EXP

Put the source code into same folder with datasets, testcase and run.sh.

```
./run.sh
```

**Single-target** : 

link: Datasets&EXP/SingleTargetTestCase

**Multiple-targets** : 

link: Datasets&EXP/MultipleTargetsTestCase

For each folder `K = x` , x represents the number of the hidden targets.

