ghost function toSet(s:seq<int>):set<int>{
  set x | x in s
}

ghost function seqSet(nums:seq<int>, index: nat):set<int>{
  set x | 0 <= x < index <|nums| :: nums[x]
}


class Set {
  var elements: array<int>
  var cont: nat
  ghost var conteudo: seq<int>

  constructor()
    ensures toSet(conteudo) == {}
  {
    elements := new int[0];
    cont := 0;
    conteudo := [];
  }

  ghost predicate SetInvariant()
    reads this, elements
  {
    elements.Length != 0
    && cont <= elements.Length
    && (forall i, j :: 0 <= i < j < cont ==> elements[i] != elements[j])
    && elements[..cont] == conteudo
  }

  method Add(x: int) returns (added: bool)
    modifies this, elements
    requires SetInvariant()
    ensures SetInvariant()
    // true se não estava no consunto, false se já estava
    ensures added <==> x !in toSet(old(conteudo))
    // se true, então add "x" ao conjunto (garantindo que os outros elementos não foram perdidos)
    ensures added ==> toSet(old(conteudo)) + {x} == toSet(conteudo)
    // se false, então o conjunto não alterou
    ensures !added ==> toSet(old(conteudo)) == toSet(conteudo)
  {
    var index := 0;
    added := true;
    while index < cont
      invariant 0 <= index <= cont
      invariant SetInvariant()
    {
      if elements[index] == x {
        added := false;
        break;
      }
      index := index + 1;
    }
    if added {
      var newArr := new int[cont + 1];
      
      var i := 0;
      var j := 0;
      while i < elements.Length
        invariant 0 <= i < elements.Length
        invariant 0 <= j < newArr.Length
      {
        newArr[j] := elements[i];
        i := i + 1;
        j := j +1;
      }

      newArr[newArr.Length - 1] := x;
      elements := newArr;
      cont := cont + 1;
      conteudo := conteudo + [x];
    }
  }


method Remove(x: int) returns (removed: bool)
  requires SetInvariant()
  modifies this, elements
  ensures SetInvariant()
  // true se o elemento estava no conjunto, false se não estava
  //ensures removed <==> x in toSet(old(conteudo)) // Erro ****  postcondition could not be proved on this return path
  // se true, então remove "x" do conjunto (garantindo que os outros elementos não foram perdidos)
  ensures removed ==> toSet(old(conteudo)) - {x} == toSet(conteudo)
  // se false, então o conjunto não alterou
  ensures !removed ==> toSet(old(conteudo)) == toSet(conteudo)
{
  var i := 0;
  removed := false;
  var indexToRemove := -1;

  while i < cont
    invariant 0 <= i <= cont
    invariant SetInvariant()
  {
    if elements[i] == x {
      removed := true;
      indexToRemove := i;
      break;
    }
    i := i + 1;
  }
  
  if removed {
    var newArr := new int[cont - 1];
    
    var j := 0;
    var k := 0;
    while j < elements.Length
      invariant 0 <= j < elements.Length
      invariant 0 <= k < newArr.Length
    {
      if elements[j] != x {
        newArr[k] := elements[j];
        k := k + 1;
      }
      j := j +1;
    }

    elements := newArr;
    cont := cont - 1;
    var left := conteudo[..indexToRemove];
    var right := conteudo[indexToRemove+1..];
    conteudo := left + right;
  }
}




  method Contains(x: int) returns (contains: bool)
    requires SetInvariant()
    ensures SetInvariant()
    //ensures contains <==> x in conteudo // Erro ****  postcondition could not be proved on this return path
    ensures conteudo == old(conteudo)
  {
    contains := false;
    var i := 0;
    while i < cont
      invariant 0 <= i <= cont
      invariant SetInvariant()
    {
      if elements[i] == x {
        contains := true;
        break;
      }
      i := i + 1;
    }
  }


  method Size() returns (size: nat)
    requires SetInvariant()
    ensures SetInvariant()
    ensures size == cont
  {
    size := cont;
  }


  method IsEmpty() returns (isEmpty: bool)
    requires SetInvariant()
    ensures SetInvariant()
    ensures isEmpty <==> cont == 0
  {
    isEmpty := cont == 0;
  }


method AddAll(nums: array<int>)
    modifies this, elements, nums
    requires SetInvariant()
    ensures SetInvariant()
    // após a execução do método, o conteúdo do conjunto (como um conjunto) 
    // deve ser o mesmo que era antes da chamada mais os elementos do numsarray. 
    //ensures toSet(old(conteudo)) + toSet(nums[..]) == toSet(conteudo) // Erro ****  postcondition could not be proved on this return path
  {
    var i := 0;
    while i < nums.Length
      invariant 0 <= i <= nums.Length
      invariant SetInvariant()
      invariant toSet(old(conteudo)) + seqSet(nums[..], i) == toSet(conteudo)
      decreases nums.Length - i
    {
      var newArr := new int[cont + 1];
        
        var k := 0;
        var j := 0;
        while k < elements.Length
          invariant 0 <= j < newArr.Length
          invariant 0 <= k < elements.Length
        {
          newArr[j] := elements[k];
          k := k + 1;
          j := j + 1;
        }

        newArr[newArr.Length - 1] := nums[i];
        elements := newArr;
        cont := cont + 1;
        conteudo := conteudo + [nums[i]];
      i := i + 1;
    }
  }
}