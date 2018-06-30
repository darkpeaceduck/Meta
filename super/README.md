### What is ?

Суперкомпиляция -- это метод оптимизации программ. Он состоит в том, что мы делаем абстрактную интерпретацию программы и пытаемся понять, какие места можно так или иначе оптимизировать. Частным случаем данного подхода является, например, тот факт, что если в программе нет свободных переменных и функций, то суперкомпилятор превращается в обычный интерпретатор.

Высокоуровнево задачу суперкомпиляции можно сформулировать так -- на вход дана программа, на выход хочется получить семантически эквивалентную, но оптимизированную ее версию.

###  Language Description

![Lang](/res/super-lang.jpg)

### Examples 
![Lang](/res/super-example.jpg)

### [Implementation based on paper](/mans/1005.5278.pdf)

### Как запускать тесты

```sh
$ ghci Test.hs
$ runTestSuite [VERBOSE]
```
### Verbose levels




0.	Pretty with subst 
1.	Pretty without subst + 0 level
2.	(show expr) + 1 level

### Table


| # | Что | Как (ИМХО) | 
| ------ | ------ | ------ |
| 3 | sum (map square ys)| OK |
| 4 | (length) ((concat) (xs)) | OK | 
| 5 | (sum) (((map) (length)) (xs)) | OK |
| 6 | ((append) (((map) (f)) (xs))) (((map) (f)) (ys)) | OK |
| 7 | ((map) (f)) (((append) (xs)) (ys)) | Сносно |
| 8 | ((filter) (pp)) (((map) (f)) (xs))] | ОК |
| 9 | ((map) (f)) (((filter) (((compose) (pp)) (f))) (xs)) | Сносно |
| 10 | ((map) (f)) ((concat) (xs)) | ОК |
| 11 | (concat) (((map) ((map) (f))) (xs)) | Сносно |
| 12 | ((iterate) (f)) ((f) (x)) | ОК |
| 13 | ((map) (f)) (((iterate) (f)) (x)) | OK |
