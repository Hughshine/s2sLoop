s2sLoop
=======

Parts of the code of my PhD

=======

文件的分类：
1. 和Loops有关的
   1. Instructions，定义了语句要复合的类型；重要的一部分是context，围绕一个语句的循环变量和全局变量
   2. Simple Language
2. 和Poly有关的
   1. PLang
   2. PolyBase
   3. Polyhedra
   4. BoxedPolyhedra
3. 公用的内存定义
   1. Memory
   2. NaiveMemory
   3. OtherMemory
4. 库
   1. ArithClasses, 定义向量，实际是一个sigma type（长度）约束的list A. 使用时常常会额外多一个维度（相比context的长度），用于仿射变换的“常数偏移”
   2. CeildFloord ?
   3. Bounds?
   4. Timestamp（？看起来很重要，做什么的？）
5. 多面体编译过程
   1. ExtractPoly
   2. PermutInstrs?
   3. Tiling
6. 证明（结论）
   1. Final
7. 没用的
   1. Lin，好像废弃了；PDep，都是注释；Lib.v，也不用关注。

重要的定义类型