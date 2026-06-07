#include "internal.hpp"
#include <string>
#include <cctype>

namespace CaDiCaL {

  int Internal::read_branch_sequence () {
    int res = 0;

    START (search);
    if (stable) { START (stable);   report ('['); }
    else        { START (unstable); report ('{'); }
    
    //-sequence <sequence-path>
    cout << "Read branching_sequence_path -sequence: " << branching_sequence_path << endl << endl << flush;
    ifstream in(branching_sequence_path);
    if (in.fail()) {cout << "The sequence file doesn't exist!" << endl; exit(0);}
    
    uint num_true = 0;
    string lit;
    
    static uint n = 0;
    
    while (!res and in >> lit) {
      ++n;
      assert(!lit.empty());
      assert(!conflict);
      
      if (lit == "R") {
        ++stats.restarts;
        backtrack(0);
        conflict = 0;
        assert (propagated == trail.size ());
        continue;
      }
      if (lit == "bt") {
        in >> lit; 
        ++n;
        assert(isdigit(lit[0]) or lit[0] == '-');
        
        if(stoi(lit) > level) {cout << endl << "-----level " << level << ", now " << stoi(lit) << ", nConf " << stats.conflicts << ", num_true " << num_true << ", stats.restarts " << stats.restarts << endl; exit(0); }
        
        backtrack(stoi(lit));
        conflict = 0;
        assert (propagated == trail.size ());
        continue;
      }
      
      assert(isdigit(lit[0]) or lit[0] == '-');
      if (!isdigit(lit[0]) and  (lit[0] != '-')) {
        cout << "lit " << lit << " ,   '" << lit[1] << "' , '" << lit.c_str()[1] << "' , " << !isdigit(lit[0]) << " , " << (lit[0] != '-') << ", n " << n << endl;
        exit(0);
      }
      
      if (val(stoi(lit)) != 0) { // should not run, because the sequence contains only the decision lits 
        ++stats.decisions;
        ++num_true;
        assert(val(stoi(lit)) == 1);
        assert(propagated == trail.size ());
        continue;
      }
      assert(!conflict);
      assert (propagated == trail.size ());
      
      ++stats.decisions;
      search_assume_decision (stoi(lit));
      propagate();
      
      if (conflict) {  // todo: analysis + when no conflict, read next(R)
        if (!level) {res = 20; cout << "conflict at dl 0!" << endl << endl << flush;}
        else {
          analyze();
          assert(!unsat);
          propagate(); // it may be still conflicting
          
          if (conflict) { 
            if (!level) {res = 20; cout << "---conflict at dl 0!" << endl << endl << flush;}
            conflict = 0;
          }
        }
      }
    }
  
    in.close();
    
    cout << "num_true:       " << num_true << endl << flush; // num_true should be 0
    assert(num_true == 0);

    if (stable) { STOP (stable);   report (']'); }
    else        { STOP (unstable); report ('}'); }

    STOP (search);

    return res;
  }
  
  
  bool Internal::has_next_lemma (ifstream& in) {
    assert(lemma.size() == 0);
    string aux; int lit;
    while (in >> aux) {
      if (aux == "d") { in >> lit; while (lit) in >> lit;}
      else if (stoi(aux) != 0) {
        lemma.push_back(stoi(aux));
        in >> lit;
        while (lit) {lemma.push_back(lit); in >> lit;}
        return true;
      }
    }
    return false;
  }
  
} //namespace CaDiCaL
