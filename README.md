# 程序语言大作业

4-30 纪要
1. 赵启元当选组长，三人明天之前都要给老师发邮件
2. 选题 VST（已经确定），参考资料为分享的github上相关教程
3. 协作方式为github共享库，按照网上教程连接
4. 五一期间先学起来，fv_tutorial.zip里面有一个基于Cygwin安装VST的教程，然后使用可以看VST_tutorial.zip里面的Tutorial.v 做Exercises.v

## 题目
使用 VST 证明带插入、查找、修改、删除、分裂、合并等操作的双向链表。

（暂定）实现目标如下：

```cpp
struct node;
struct list;
struct node * begin(struct list * );
struct node * end(struct list * );
struct node * next(struct node * );
struct node * rbegin(struct list * );
struct node * rend(struct list * );
struct node * rnext(struct node * );
void push_back (struct list *, int );
void pop_back (struct list * );
void push_front (struct list *, int );
void pop_front (struct list * );
struct list * merge (struct list * x, struct list * y);
struct list * split (struct list * x, struct node * y);
```

以上接口并不固定，只要能很好的实现功能即可。
