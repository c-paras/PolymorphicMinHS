# PolymorphicMinHS
Type inference for the polymorphic MinHS programming language, a subset of Haskell

This implementation has been tested on Ubuntu 64-bit 16.04 LTS using GHC version 7.10.3. Convenient testing can be done in one of three ways:

* Build system and run all tests:

```
reset && cabal build && ./run_tests.sh
```

* Test a standalone program in `ghci`:

```haskell
let program = "main = 0;"
let Right e = parseProgram "<input>" program
infer e
```

* Specify a MinHS program as a string:

```
./check.sh "<program>"
```

Copyright (C) 2016 Constantinos Paraskevopoulos

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
