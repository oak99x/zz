class Set {
  var elements: array<int>;
  ghost var abstractSet: set<int>; // Representação abstrata do conjunto

  constructor() {
      elements := new int[0];
      abstractSet := {};
  }

// Essa invariante define uma relação entre a representação abstrata `abstractSet` do conjunto e os elementos armazenados no array `elements`. 
// Em partes:
// 1. `abstractSet` é a representação abstrata do conjunto
//     - Essa é a representação do conjunto que queremos manter consistente. 
//     - É o que a classe `Sett` deve representar como um conjunto de inteiros.
// 2. `{i: int | ...}` é uma notação usada para denotar um conjunto de elementos `i` que satisfazem uma determinada condição. 
//     - Neste caso, estamos criando um conjunto de inteiros `i`, que serão os elementos no conjunto representado por `abstractSet`.
// 3. `exists (j: int :: 0 <= j < elements.Length && elements[j] == i)` é a condição que cada elemento `i` no conjunto `abstractSet` deve satisfazer. 
//     - Isso significa que para cada `i` no conjunto `abstractSet`, deve existir um índice `j` no array `elements` tal que:
//     - `0 <= j < elements.Length`: O índice `j` deve estar dentro dos limites do array `elements`.
//     - `elements[j] == i`: O elemento no índice `j` do array `elements` deve ser igual a `i`.
  // predicate SetInvariant() {
  //   // Invariante para a representação abstrata associada à coleção do tipo conjunto.
  //   abstractSet == {i: int | exists (j: int :: 0 <= j < elements.Length && elements[j] == i)}; //erro diz que falta uma "}"
  // }

  ghost predicate SetInvariant()
    reads this, elements
  {
    // Garante que não há elementos duplicados no conjunto
    forall i, j :: 0 <= i < elements.Length && 0 <= j < elements.Length && i != j ==> elements[i] != elements[j]
    && elements[..elements.Length] == elements
  }

  method Add(element: int) returns (added: bool)
    modifies elements
    ensures SetInvariant()
  {
    var index := 0;
    while (index < elements.Length)
      invariant 0 <= index <= elements.Length
      invariant SetInvariant()
    {
      if (elements[index] == element) {
        added := false;
        return;
      }
      index := index + 1;
    }
    var newElements := new int[elements.Length + 1];
    newElements[newElements.Length - 1] := element;
    elements := newElements;
    added := true;
  }

  // method Remove(element: int) returns (removed: bool)
  //   ensures SetInvariant()
  // {
  //   var index := 0;
  //   while (index < elements.Length)
  //     invariant 0 <= index <= elements.Length
  //     invariant SetInvariant()
  //   {
  //     if (elements[index] == element) {
  //       elements := elements[..index] + elements[index + 1..]; //linha com erro
  //       removed := true;
  //       return;
  //     }
  //     index := index + 1;
  //   }
  //   removed := false;
  // }

  method Contains(element: int) returns (contains: bool)
    ensures SetInvariant()
  {
    var index := 0;
    while (index < elements.Length)
      invariant 0 <= index <= elements.Length
      invariant SetInvariant()
    {
      if (elements[index] == element) {
        contains := true;
        return;
      }
      index := index + 1;
    }
    contains := false;
  }

  method Count() returns (count: int)
    ensures SetInvariant()
  {
    count := elements.Length;
  }

  method IsEmpty() returns (empty: bool)
    ensures SetInvariant()
  {
    empty := elements.Length == 0;
  }

  method AddAll(arr: array<int>)
    modifies arr
    requires arr != null
    ensures SetInvariant()
  {
    var index := 0;
    while (index < arr.Length)
      invariant 0 <= index <= arr.Length
      invariant SetInvariant()
    {
      var element := arr[index];
      var contains := Contains(element);
      if (!contains) {
        var add := Add(element);
      }
      index := index + 1;
    }
  }
}

method Main() {
  var s := new Set();
  var result: bool;
  var count: int;

  result := s.IsEmpty();
  assert result == true;

  result := s.Add(1); // adiciona o 1
  assert result == true;

  result := s.Add(1); // não pode adicionar o 1 de novo
  assert result == false;

  // s.Remove(2);
  // result := s.Remove(3);
  // assert result == false;


  count := s.Count();
  assert count == 1;

  var elements := new int[3];
  elements[0] := 2;
  elements[1] := 3;
  elements[2] := 4;
  s.AddAll(elements);
  count := s.Count();
  assert count == 4;
}

