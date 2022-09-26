s2sLoop
=======

Parts of the code of my PhD

=======

文件的分类：
1. 和Loops有关的
   1. Instructions，定义了语句要复合的类型；重要的一部分是context，围绕一个语句的循环变量和全局变量
   2. Simple Language，
2. 和Poly有关的
   1. PLang：Poly语言的定义
   2. PolyBase
      1. 看起来定义了“不等式”及其变换，应该最主要对应domain
   3. Polyhedra：不是主要的放置定义的文件，似乎不用特别关注
   4. BoxedPolyhedra。不是特别看得懂，看起来是关于有参数限制的多面体。
3. 公用的内存定义
   1. Memory
      1. `BASEMEM`, 用类型CELL索引MEM，CELL包含array ident和一个index list.
      2. memory layout
      3. Module MEMORY: 给了关于BASEMEM得一些额外的证明，比如相同的内存等
   2. OtherMemory
      1. 尝试把Clight Memory Model放进来。感觉定义有一些问题. 是Loops和Poly使用的真正的Memory.
         1. 但看起来实际用的不是这个...？
4. 库
   1. ArithClasses, 定义向量，实际是一个sigma type（长度）约束的list A. 使用时常常会额外多一个维度（相比context的长度），用于仿射变换的“常数偏移”
   2. CeildFloord ?
   3. Bounds?
      1. 定义每一重循环的上下界，辅助用
      2. 定义了一些工具类
   4. Timestamp（？看起来很重要，做什么的？）
      1. 看起来是和schedule有关，具体是什么关系？
      2. 是给“Instruction_Point”用的，也就是每个instance. schedule 为domain中的每个点赋予了一个 timestamp. Poly的语义，建立在instruction point的语义之上，额外多个排序.
5. 多面体编译过程
   1. ExtractPoly: 看起来就是codegen倒着做，没什么特别的
   2. Tiling
6. 证明（结论）
   1. PermutInstrs?：change_schedule这个函数和似乎是为了change_schedule_OK这个定理
      1. 似乎和validate有关
   2. Final: top lemma
7. 没用的
   1. Lin，好像废弃了；PDep，都是注释；Lib.v，也不用关注。
   2. NaiveMemory
      1. 和代码无关
   3. OcamlInterface: 和形式化无关
重要的定义类型

---

1. 我需要知道validator是如何保证的，change_schedule/mk_tilled_poly做了什么。