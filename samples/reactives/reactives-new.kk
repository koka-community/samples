named div effect rref<s::S, a::V> in providerHeap<s>
  fun emit(a: a): ()
  ctl watch_<b,e>(p: provider<s,b,e>, immediate: bool): b
  ctl yield(): ()

scoped div effect providerHeap<s::S>
  ctl mkProvider<a,e>(reactor: ev<rref<s,a>> -> <pure,providerHeap<s>,st<global>|e> a, name: string, show: (a) -> <pure,providerHeap<s>,st<global>|e> string): provider<s,a,e>

fun watch(r: ev<rref<s,a>>, p: provider<s,b,e>, immediate: bool = True): <pure,providerHeap<s>,st<global>> b
  r.watch_(p, immediate)

div type provider<s,a,e>
  Provider(
    listeners: ref<global, list<(a) -> <pure,providerHeap<s>,st<global>|e> ()>>,
    current: () -> <pure,providerHeap<s>,st<global>|e> a,
    r: ref<global, maybe<ev<rref<s,a>>>>,
    name: string
  )

fun heap(action: forall<s> () -> <providerHeap<s>,st<global>,pure|e> ()): <st<global>,pure|e> ()
  with handler
    ctl mkProvider(reactor, pname, show)
      val lcurrent  : some<a> ref<global, maybe<a>> = ref(Nothing)
      val r  =  ref(Nothing)
      val listeners0 = ref(Nil)
      val continuex = ref(fn(){})
      val doInit = fn(r1)
          trace("doInit")
          r1.yield()
          trace("doneYield")
          val x = reactor(r1)
          r1.emit(x)
          x
      with x <- named handler
        fun emit(a)
          lcurrent := Just(a)
          ("emitting " ++ show(a)).trace
          (!listeners0).foreach fn(l)
            l(a)
        ctl yield()
          ("yielding from " ++ pname).trace
          continuex := (fn() {resume(())})
        ctl watch_(o:some<s,b,e> provider<s,b,e>, triggerImmediately)
          (pname ++ " watching " ++ o.name).trace
          o.listeners.set(Cons(fn(b) {resume(b)}, !(o.listeners)))
          if triggerImmediately then
            (o.current)()
            ()
      r.set(Just(x))
      val provider = Provider(listeners0, fn(){ 
        match !lcurrent
          Nothing -> 
            match !r
              Just(r') -> 
                "initializing".trace
                val x' = doInit(r')
                x'.show.trace 
                x'
              Nothing -> throw("Provider " ++ providerName ++ " not initialized")
          Just -> 
            "continuing".trace
            (!continuex)()
            match !lcurrent
              Just(k') -> k'
        },
        r, providerName)
      resume(provider)
  action()  
 

fun main()
  val result = try
    with heap
    val oProvider = mkProvider(
      fn(r: ev<rref<s,int>>) {
        r.emit(1)
        r.emit(2)
        0
      },
      fn (x: int) x.show,
      "o"
    )
    val sProvider = mkProvider(
      fn(r: ev<rref<s,int>>){
        trace("Hi")
        r.emit(100)
        val x = r.watch(oProvider, True)
        trace("X: " ++ x.show)
        1
      },
      fn(x:int) x.show,
      "s"
    );
    (sProvider.current)().show.trace
  match result
    Ok(x) -> x.show
    Error(e) -> e.show