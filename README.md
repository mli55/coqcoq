# 程序语言大作业

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

## 开发日志

4-30 纪要

1. 赵启元当选组长，三人明天之前都要给老师发邮件
2. 选题 VST（已经确定），参考资料为分享的github上相关教程
3. 协作方式为github共享库，按照网上教程连接
4. 五一期间先学起来，fv_tutorial.zip里面有一个基于Cygwin安装VST的教程，然后使用可以看VST_tutorial.zip里面的Tutorial.v 做Exercises.v

5-7 纪要

1. 基本完成 C 程序实现
2. 初步设计了双向链表的内存表示
3. 完成了 `list_new` 和 `list_free` 的证明

## 注意事项

在正式编译相关文件之前，请先保证根目录下包含以下文件：

### `_CoqProject`

该文件应包含类似以下的内容：
```
-Q . DL
-Q ../../../../VST/msl VST.msl
-Q ../../../../VST/sepcomp VST.sepcomp
-Q ../../../../VST/veric VST.veric
-Q ../../../../VST/floyd VST.floyd
-Q ../../../../VST/progs VST.progs
-R ../../../../VST/compcert compcert
```

第一行定义了该项目逻辑目录的名称，后面几行声明了 VST 的所在位置。

### `CONFIGURE`

该文件应包含类似以下的内容：
```
COQBIN=/cygdrive/D/Coq/bin/
VST_DIR=../../VST
NEED_VST=true
```

第一行声明了 Coq 的安装位置，第二行声明了 VST 的所在位置，第三行声明了需要 VST 进行开发。