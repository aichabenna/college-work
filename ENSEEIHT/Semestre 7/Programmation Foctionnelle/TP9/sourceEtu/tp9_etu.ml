
module type DELIMCC = sig
  type 'a prompt
  val new_prompt : unit -> 'a prompt
  val push_prompt : 'r prompt -> (unit -> 'r) -> 'r
  val shift : 'r prompt -> (('s -> 'r) -> 'r)-> 's
end

module TP (Delimcc : DELIMCC) = struct
  
  module GreenThreads =
    struct
      (* à compléter/modifier *)
      type program = unit -> unit
      type res =
          | Exit
          | Yield of continuation
          | Fork of program * continuation
      and  continuation = unit -> res

      let prompt : res Delimcc.prompt = Delimcc.new_prompt()

      let scheduler proc_init = 
        let waiting = Queue.create () in
        let rec spawn prog =
          handle (Delimcc.push_prompt prompt (fun () -> prog () ; Exit))
        and handle result = match result with
          | Exit -> if Queue.is_empty waiting then () else handle (Queue.pop waiting ())
          | Yield k -> 
              Queue.push k waiting;
              handle (Queue.pop waiting ())
          | Fork(p, k) -> 
              Queue.push k waiting;
              spawn p
        in spawn proc_init

      let yield () : unit = Delimcc.shift prompt (fun k -> Yield k);;
      let fork (proc : program) : unit  = Delimcc.shift prompt (fun k -> Fork (proc, k));;
      let exit () : unit = Delimcc.shift prompt (fun _ -> Exit);;

    end

  module type Channel =
    sig
      val create : unit -> ('a -> unit) * (unit -> 'a)
    end

  module GTChannel : Channel =
    struct
      (* à compléter/modifier *)
      let create () = assert false;;
    end
      
  let sieve () =
    let rec filter reader =
      GreenThreads.(
        let v0 = reader () in
        if v0 = -1 then exit () else
        Format.printf "%d@." v0;
        yield ();
        let (writer', reader') = GTChannel.create () in
        fork (fun () -> filter reader');
        while true
        do
          let v = reader () in
          yield ();
          if v mod v0 <> 0 then writer' v;
          if v = -1 then exit ()
        done
      ) in
    let main () =
      GreenThreads.(
        let (writer, reader) = GTChannel.create () in
        fork (fun () -> filter reader);
        for i = 2 to 1000
        do
          writer i;
          yield ()
        done;
        writer (-1);
        exit ()
      ) in
    GreenThreads.scheduler main;;
end
