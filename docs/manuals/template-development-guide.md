# Руководство по разработке шаблонов

*   [Базовые шаблон](#basetemplate)
    *   [Элементы базового шаблона](#elements)
        *   [Препараторы](#preparators)
*   [Генерация тестов](#testgen)
    *   [Команда запуска генератора](#testgenrun)

## Базовый шаблон


### Элементы базового шаблона


#### Препараторы


## Генерация тестов

Пример команды для ОС Windows:

```
%MICROTESK_HOME%\bin\generate.bat riscv algorithms/integer/int_euclid.rb --code-file-prefix algorithms/integer --code-file-extension s -v --ri RV64FULL
```