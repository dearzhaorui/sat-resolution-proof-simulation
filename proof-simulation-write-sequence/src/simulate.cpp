#include "internal.hpp"

namespace CaDiCaL {

  bool Internal::is_provable(vector<int>& c) {
    assert(!level);
    assert(!conflict);
    assert(propagated == trail.size());
    bool provable = false;
    
    if (!propagate2()) provable = true;
    
    for (uint i = 0; not provable and i < c.size(); ++i) {
      if (val(c[i]) == 1) provable = true; // if true, we cannot set if to false --> we have a conflict
      else if (val(c[i]) == 0) { // if undef --> set it to false [if false, ignore]
        search_assume_decision(-c[i]); // next decision
        
        int propagated2 = propagated;
        if (!propagate2()) provable = true; // propagation gave a conflict       
        
        if(!conflict) {
          [[maybe_unused]] uint ts=trail.size();
          propagated = propagated2;
          propagate();
          assert(!conflict);
          assert(ts == trail.size());
        }
        
      }
    }
    
    // Don't directly backtract to dl 0 in order to reuse trail
    //if (provable) {
      //backtrack(0);
      //conflict = 0;
      //assert(!level);
    //}
    return provable;
  }

  
  bool Internal::is_empowering_wrt_lit_no_bt (vector<int>& c, int idx) {
    assert(!conflict);
    if(isUnit(c[idx])) return false;
    else assert(val(c[idx]) == 0); // undef
    //assert(!level);
    bool conf_found = false;
    int numDecs = 0;
    assert(propagated == trail.size());
    if (!propagate()) conf_found = true;
    
    for (uint i = 0; not conf_found and i < c.size(); ++i) {
      if (int(i) == idx) continue;

      if (val(c[i]) == 1) conf_found = true; // if true, it is not 1-empowering
      else if (val(c[i]) == 0) { // if undef --> set it to false and prop. If false --> skip it
        ++numDecs;
        ++stats.decisions;
        search_assume_decision(-c[i]); // next decision
        if (!propagate()) {conf_found = true; backtrack(level-1);} // propagation gave a conflict                     
      }
    }

    [[maybe_unused]] bool is_empowering = (not conf_found and val(c[idx]) == 0);
    //backtrack(0); // BT to dl zero
    conflict = 0;
    //assert(!level);
    
    if (c.size() > 1) {
      if (is_empowering) ++numDecs;
      stats.sumPercDecs += (double)numDecs/c.size();
      ++stats.sumNumLemmas;
    }
    
    return is_empowering;
  }
  
  bool Internal::is_empowering_wrt_lit_no_bt2 (vector<int>& c, int idx) {
    assert(!conflict);
    if(isUnit(c[idx])) return false;
    else assert(val(c[idx]) == 0); // undef
    
    bool conf_found = false;
    int numDecs = 0;
    assert(propagated == trail.size());
    if (!propagate2()) conf_found = true;
    
    for (uint i = 0; not conf_found and i < c.size(); ++i) {
      if (int(i) == idx) continue;

      if (val(c[i]) == 1) conf_found = true; // if true, it is not 1-empowering
      else if (val(c[i]) == 0) { // if undef --> set it to false and prop. If false --> skip it
        ++numDecs;
        ++stats.decisions;
        search_assume_decision(-c[i]); // next decision
        if (!propagate2()) {conf_found = true; backtrack(level-1); } // propagation gave a conflict                     
      }
    }

    [[maybe_unused]] bool is_empowering = (not conf_found and val(c[idx]) == 0);
    //backtrack(0); // BT to dl zero
    conflict = 0;
    //assert(!level);
    
    if (c.size() > 1) {
      if (is_empowering) ++numDecs;
      stats.sumPercDecs += (double)numDecs/c.size();
      ++stats.sumNumLemmas;
    }
    
    return is_empowering;
  }
  
  bool Internal::is_empowering_wrt_lit_no_bt_revert (vector<int>& c, int idx) {
    assert(!conflict);
    if(isUnit(c[idx])) return false;
    else assert(val(c[idx]) == 0); // undef
    //assert(!level);
    bool conf_found = false;
    int numDecs = 0;
    assert(propagated == trail.size());
    if (!propagate()) conf_found = true;
    
    for (int i = int(c.size()-1); not conf_found and i >= 0; --i) {
      if (i == idx) continue;

      if (val(c[i]) == 1) conf_found = true; // if true, it is not 1-empowering
      else if (val(c[i]) == 0) { // if undef --> set it to false and prop. If false --> skip it
        ++numDecs;
        ++stats.decisions;
        search_assume_decision(-c[i]); // next decision
        if (!propagate()) {conf_found = true; backtrack(level-1);} // propagation gave a conflict                     
      }
    }

    [[maybe_unused]] bool is_empowering = (not conf_found and val(c[idx]) == 0);
    conflict = 0;
    assert(is_empowering);
    
    if (c.size() > 1) {
      if (is_empowering) ++numDecs;
      stats.sumPercDecs += (double)numDecs/c.size();
      ++stats.sumNumLemmas;
    }
    
    return is_empowering;
  }
  
  bool Internal::is_empowering_wrt_lit_no_bt2_revert (vector<int>& c, int idx) {
    assert(!conflict);
    if(isUnit(c[idx])) return false;
    else assert(val(c[idx]) == 0); // undef
    
    bool conf_found = false;
    assert(propagated == trail.size());
    if (!propagate2()) conf_found = true;
    
    for (int i = int(c.size()-1); not conf_found and i >= 0; --i) {
      if (i == idx) continue;

      if (val(c[i]) == 1) conf_found = true; // if true, it is not 1-empowering
      else if (val(c[i]) == 0) { // if undef --> set it to false and prop. If false --> skip it
        ++stats.decisions;
        search_assume_decision(-c[i]); // next decision
        if (!propagate2()) {conf_found = true; backtrack(level-1); } // propagation gave a conflict                     
      }
    }

    [[maybe_unused]] bool is_empowering = (not conf_found and val(c[idx]) == 0);
    conflict = 0;
    
    return is_empowering;
  }
  
  bool Internal::is_empowering_wrt_lit_no_bt_other_first (vector<int>& c, int idx, int p, vector<int>& possible_empow_lit_idx) {
    assert(!conflict);
    if(isUnit(c[idx])) return false;
    else assert(val(c[idx]) == 0); // undef
    bool conf_found = false;
    int numDecs = 0;
    assert(propagated == trail.size());
    if (!propagate()) conf_found = true;

    // propagate the imlpossible empow lits if it exists after bt, and the previous unmarked absorbed empow lit
    for (int i = 0; not conf_found and i < (int)lemma.size(); ++i) {
    //for (int i = int(lemma.size()-1); not conf_found and i >= 0; --i) {
      int lit = lemma[i];
      if (!possi_empow_lit(lit)) { // not marked
        assert(val(lit) != 1); // otherwise, there is a conflict
        if (val(lit) == 0) {
          out << -lit << " " << flush;
          ++numDecs;
          ++stats.decisions;
          ++stats.decisionsSimRead;
          search_assume_decision(-lit); // next decision
          if (!propagate()) {conf_found = true; backtrack(level-1); }
        }
      }
    }
    // propagate other possible empow lits, except for the current empow lit
    for (uint k = p+1; not conf_found and k < possible_empow_lit_idx.size(); ++k) {
    //for (int k = int(possible_empow_lit_idx.size()-1); not conf_found and k > p; --k) {
      int posi_idx = possible_empow_lit_idx[k];
      int lit = lemma[posi_idx];
      assert(possi_empow_lit(lit));
      
      if (val(lit) == 1) conf_found = true; // if true, it is not 1-empowering
      else if (val(lit) == 0) { // if undef --> set it to false and prop. If false --> skip it
        out << -lit << " " << flush;
        ++numDecs;
        ++stats.decisions;
        ++stats.decisionsSimRead;
        search_assume_decision(-lit); // next decision
        if (!propagate()) {conf_found = true; backtrack(level-1); } // propagation gave a conflict                       
      }
    }

    [[maybe_unused]] bool is_empowering = (not conf_found and val(c[idx]) == 0);
    conflict = 0;
    
    if (c.size() > 1) {
      if (is_empowering) ++numDecs;
      stats.sumPercDecs += (double)numDecs/c.size();
      ++stats.sumNumLemmas;
    }
    
    return is_empowering;
  }
  

  void Internal::set_other_lits_to_false_and_propagate ([[maybe_unused]] const int idx, const int p, vector<int>& possible_empow_lit_idx, int nDecs) {
    
    bool conf_found = false;
    int propagated2;
    
    // propagate the imlpossible empow lits if it exists after bt, and the previous unmarked absorbed empow lit
    for (int k = 0; !conflict and k < (int)lemma.size(); ++k) {
    //for (int k = int(lemma.size()-1); !conflict and k >= 0; --k) {
      int lit = lemma[k];
      if (!possi_empow_lit(lit)) { // not marked
        assert(possi_empow_lit(lit) <= 0);
        assert(val(lit) != 1); // otherwise, there is a conflict
        assert(k != idx);
        if (val(lit) == 0) {
          out << -lit << " " << flush;
          ++nDecs;
          ++stats.decisions;
          ++stats.decisionsSimRead;
          search_assume_decision(-lit); // next decision
          propagated2 = propagated;
          propagate();
          assert(!conflict);
          [[maybe_unused]] uint ts = trail.size();
          propagated = propagated2;
          propagate2();
          assert(!conflict);
          assert(ts == trail.size());
          
        }
      }
    }
    //checkAllClausesPropagated();
    
    // propagate other possible empow lits, except for the current empow lit
    for (uint k = p+1; not conf_found and k < possible_empow_lit_idx.size(); ++k) {
    //for (uint k = possible_empow_lit_idx.size()-1; not conf_found and k > p; --k) {
      int posi_idx = possible_empow_lit_idx[k];
      int lit = lemma[posi_idx];
      assert(possi_empow_lit(lit));
      
      if (val(lit) == 1) conf_found = true; // if true, it is not 1-empowering
      else if (val(lit) == 0) { // if undef --> set it to false and prop. If false --> skip it
        out << -lit << " " << flush;
        ++nDecs;
        ++stats.decisions;
        ++stats.decisionsSimRead;
        propagated2 = propagated;
        search_assume_decision(-lit); // next decision
        if (!propagate()) conf_found = true; // propagation gave a conflict      
        [[maybe_unused]] uint ts = trail.size();
        propagated = propagated2;
        propagate2();
        assert(!conflict);
        assert(ts == trail.size());
      }
    }
    
    assert(propagated == trail.size());
    assert(not conf_found and val(lemma[idx]) == 0);
    
    //if(conf_found or val(lemma[idx]) != 0) {
      //cout << endl << "error: conf_found? " << conf_found << ", val = " << (int)val(lemma[idx]) << ", level " << level << endl;
      //exit(0);
    //}
    
  }
  
  void Internal::propagate_false_other_possible_empowering_lits (const int p, vector<int>& possible_empow_lit_idx, int& nDecs) {
    bool conf_found = false;
    // propagate other possible empow lits, except for the current empow lit
    //for (uint k = p+1; not conf_found and k < possible_empow_lit_idx.size(); ++k) {  
    for (int k = (int)possible_empow_lit_idx.size()-1; not conf_found and k > p; --k) { // this reverse order seems slightly better
      int posi_idx = possible_empow_lit_idx[k];
      int lit = lemma[posi_idx];
      assert(possi_empow_lit(lit));
      
      if (val(lit) == 1) conf_found = true; // if true, it is not 1-empowering
      else if (val(lit) == 0) { // if undef --> set it to false and prop. If false --> skip it
        out << -lit << " " << flush;
        ++nDecs;
        ++stats.decisions;
        ++stats.decisionsSimRead;
        int propagated2 = propagated;
        search_assume_decision(-lit); // next decision
        if (!propagate()) conf_found = true; // propagation gave a conflict      
        [[maybe_unused]] uint ts = trail.size();
        propagated = propagated2;
        propagate2();
        assert(!conflict);
        assert(ts == trail.size());
      }
    }
    
    assert(propagated == trail.size());
    assert(not conf_found and val(lemma[possible_empow_lit_idx[p]]) == 0); // current empow lit is undef
  }

  // Propagate the duplicated DB: propagate2()
  bool Internal::is_empowering_wrt_lit_no_bt2_other_first (vector<int>& c, int idx, int p, vector<int>& possible_empow_lit_idx) {
    assert(!conflict);
    if(isUnit(c[idx])) return false;
    else assert(val(c[idx]) == 0); // undef
    bool conf_found = false;
    assert(propagated == trail.size());
    if (!propagate2()) conf_found = true;
    assert(possi_empow_lit(c[idx]));
    // propagate the imlpossible empow lits if it exists after bt, and the previous unmarked absorbed empow lit
    for (int i = int(lemma.size()-1); not conf_found and i >= 0; --i) {
      int lit = lemma[i];
      if (not possi_empow_lit(lit)) { // not marked
        assert(possi_empow_lit(lit) <= 0);
        assert(i != idx);
        if (val(lit) == 1) conf_found = true;
        else if (val(lit) == 0) {
          ++stats.decisions;
          search_assume_decision(-lit); // next decision
          if (!propagate2()) { conf_found = true; backtrack(level-1); }
        }
      }
    }
    // propagate other possible empow lits, except for the current empow lit
    for (int k = int(possible_empow_lit_idx.size()-1); not conf_found and k > p; --k) {
      int posi_idx = possible_empow_lit_idx[k];
      int lit = lemma[posi_idx];
      assert(possi_empow_lit(lit));
      
      if (val(lit) == 1) conf_found = true; // if true, it is not 1-empowering
      else if (val(lit) == 0) { // if undef --> set it to false and prop. If false --> skip it
        ++stats.decisions;
        search_assume_decision(-lit); // next decision
        if (!propagate2()) {conf_found = true; backtrack(level-1);} // propagation gave a conflict                       
      }
    }

    [[maybe_unused]] bool is_empowering = (not conf_found and val(c[idx]) == 0);
    conflict = 0;
    
    return is_empowering;
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
  
  void Internal::scan_possible_empow_lit (vector<int>& c, vector<int>& idx_v) {
    for (uint i = 0; i < c.size(); ++i) {
      assert(level >= 0);
      if (val(c[i]) != 0) {
        int lit_level = var(c[i]).level;
        assert(lit_level >= 0);
        
        if(lit_level > 0) backtrack(lit_level-1); // make sure the checked lit is undef now. except units
        assert(lit_level == 0 or val(c[i]) == 0);
      }
      
      [[maybe_unused]] bool is_emp = is_empowering_wrt_lit_no_bt2_revert(c, i);
      
      if (is_emp) idx_v.push_back(i);
    }
    
  }

  
  bool Internal::read_next_lemma (ifstream& in, bool& deleted) {
    deleted = false;
    assert(lemma.size() == 0);
    string aux; int lit;
    while (in >> aux) {
      if (aux == "d") {
        deleted = true; 
        in >> lit; 
        while (lit) {lemma.push_back(lit); in >> lit;}
        return true;
      }
      else if (stoi(aux) != 0) {
        lemma.push_back(stoi(aux));
        in >> lit;
        while (lit) {lemma.push_back(lit); in >> lit;}
        return true;
      }
    }
    return false;
  }
  
  bool Internal::clause_subsume_lits (Clause *c, vector<int>& lits) {
    mark (c);
    int needed = c->size;
    for (auto &lit : lits) {
      if (marked (lit) <= 0)
        continue;
      if (!--needed)
        break;
    }
    unmark (c);  
      
    return needed == 0;
  }
  
  bool Internal::lits_equal_to_lits (vector<int>& a, vector<int>& b) {
    assert(a.size() == b.size());
    sort(a.begin(), a.end(), [](const int& l1, const int& l2) {return abs(l1) < abs(l2);});
    
    // already sorted
    //sort(b.begin(), b.end(), [](const int& l1, const int& l2) {return abs(l1) < abs(l2);});
    for (uint i = 0; i < a.size(); ++i) if(a[i] != b[i]) return false;
    return true;
  }
  
  bool Internal::clause_equal_to_lits (Clause *c, vector<int>& lits) {
    assert(c->size == (int)lits.size());
    vector<int> a;
    for(auto& l : *c) a.push_back(l);
    return lits_equal_to_lits(a, lits);
  }
  
  void Internal::check_and_count(Clause *c, vector<int>& lemma_sorted, int& numSameSize, int& numSameLemma, int& numShorterLemma, int& numSubsumeLemma, bool& found_equal_lemma ) {
    
    if(!c && lemma_sorted.size() == 1) {++numSameSize; ++numSameLemma; return;}
    if(!c) return;
    
    assert(!found_equal_lemma);
    if(c->size == (int)lemma_sorted.size()) {
      ++numSameSize;
      if (clause_equal_to_lits(c, lemma_sorted)) {
        found_equal_lemma = true; 
        ++numSameLemma;
      }
    }
    else if (c->size < (int)lemma_sorted.size()) {
      ++numShorterLemma;
      if (clause_subsume_lits(c, lemma_sorted)) {
        ++numSubsumeLemma;
        found_equal_lemma = true;
      }
    }
  }
  
  // only check the original DB and the copied DB
  void Internal::checkAllClausesPropagated () {
    assert(propagated == trail.size());
    int n = -1;
    for (Clause* c: clauses) {
      ++n;
      if (c->garbage) continue;
      bool isTrue = false;
      int numUndef = 0;
      for(int& l : *c) {
        if (val(l) == 1) {isTrue = true; break;}
        else if (val(l) == 0) {++numUndef; if(numUndef >= 2) break;}
      }
      if (isTrue) continue;
      if (numUndef < 2) {
        cout << endl << endl << "numCoreLemmas " << numCoreLemmas << ", Clause " << n << " is not completely propagated, numUndef " << numUndef << ", level " << level << " nDecs " << stats.decisions << " ,nConfs " << stats.conflicts << endl;
        for(auto& l : *c) cout << l << ",v" << (int)val(l) << ",lv" << (val(l)!=0? var(l).level : (-1)) << " ";
        cout << endl;
        exit(0);
      }
    }
  }
  
  // only check the copied DB
  void Internal::checkAllClausesPropagated_in_copiedDB () {
    assert(propagated == trail.size());
    int n = -1;
    for (Clause* c: clauses) {
      ++n;
      if (n%2 == 0)   continue;
      if (c->garbage) continue;
      bool isTrue = false;
      int numUndef = 0;
      for(int& l : *c) {
        if (val(l) == 1) {isTrue = true; break;}
        else if (val(l) == 0) {++numUndef; if(numUndef >= 2) break;}
      }
      if (isTrue) continue;
      if (numUndef < 2) {
        cout << endl << endl << "numCoreLemmas " << numCoreLemmas << ", Clause " << n << " is not completely propagated, numUndef " << numUndef << ", level " << level << " nDecs " << stats.decisions << " ,nConfs " << stats.conflicts << endl;
        for(auto& l : *c) cout << l << ",v" << (int)val(l) << ",lv" << (val(l)!=0? var(l).level : (-1)) << " ";
        cout << endl;
        exit(0);
      }
    }
  }
  
  // only check the original DB
  void Internal::checkAllClausesPropagated_in_originalDB () {
    assert(propagated == trail.size());
    int n = -1;
    for (Clause* c: clauses) {
      ++n;
      if (n%2 == 1)   continue;
      if (c->garbage) continue;
      bool isTrue = false;
      int numUndef = 0;
      for(int& l : *c) {
        if (val(l) == 1) {isTrue = true; break;}
        else if (val(l) == 0) {++numUndef; if(numUndef >= 2) break;}
      }
      if (isTrue) continue;
      if (numUndef < 2) {
        cout << endl << endl << "numCoreLemmas " << numCoreLemmas << ", Clause " << n << " is not completely propagated, numUndef " << numUndef << ", level " << level << " nDecs " << stats.decisions << " ,nConfs " << stats.conflicts << endl;
        for(auto& l : *c) cout << l << ",v" << (int)val(l) << ",lv" << (val(l)!=0? var(l).level : (-1)) << " ";
        cout << endl;
        exit(0);
      }
    }
  }



//./build/cadical --chrono=0 --compact=0 --decompose=0 -sequence sequence.txt -core ../proof-simulation-read-sequence/core.txt  cnf/add16.cnf prf.txt

// optimized version: Use trail between multiple empow. lits and more than 1 analysis
  int Internal::write_sequence_reuse_trail_scan_empoLits_revert () { // check properties, return #clauses that are both empowering and provable
 
    int res = 0;

    START (search);

    if (stable) { START (stable);   report ('['); }
    else        { START (unstable); report ('{'); }
    
    cout << endl << "writing to branching_sequence_path: " << branching_sequence_path<< endl;
    if (core_lemmas_path == "") {cout << "error: No core lemma file specified!" << endl; exit(1);} 
    if (branching_sequence_path == "") {cout << "error: No branching_sequence_path specified!" << endl; exit(1);} 
    cout << "core_lemmas_path: " << core_lemmas_path << endl << endl;
  
    ifstream in(core_lemmas_path);
    if (in.fail()) {cout << "The core file doesn't exist!" << endl; exit(0);}
  
    out = ofstream(branching_sequence_path);
    
    bool count = true;
    
    uint numCoreLemmas = 0;
    uint numProvableAndEmpower = 0;
    size_t sumNumEmpowerLits = 0, sumNumEmpowerLitsWithMultiAnalysis = 0;
    
    uint64_t sumNumAnalysis = 0;
    uint numOnly1EmpoLit = 0, numOnly1LitIsFirst = 0;
    
    int numSameSize = 0, numSameLemma = 0, numShorterLemma = 0, numSubsumeLemma = 0;
    uint trueLitNotPrinted = 0;
    uint numNotBacktrackTo0 = 0, numLevelsReused = 0;
    
    uint numEmpowChecksIfNoConf = 0, numIsStillEmpowIfNoConf = 0;
  
    while (!res and has_next_lemma(in)) {
      assert(!conflict);
      assert(!level);
      ++numCoreLemmas;
      
      if(lemma.size() == 1 and val(lemma[0]) == -1) { // not provable, benchmark: add128.cnf -chrono=1
        out << lemma[0] << endl;
        cout << "found core lemma is unit " << lemma[0] << ", and it's false!" << endl;
        res = 20;
        continue;
      }
      //assert(is_provable(lemma)); // this is the property of all lemmas

  // ------------- scan possible empowing lits ------------------
      vector<int> possible_empow_lit_idx;
      scan_possible_empow_lit(lemma, possible_empow_lit_idx); // use DB2
  // ------------------------------------------------------------
  
      backtrack(0);
      if (possible_empow_lit_idx.size() == 0) {
        lemma.clear();
        continue;
      }
      
      int numEmpowerLits = 0, numEmpowerLitsWithMultiAnalysis = 0;
      int numAnalysis = 0;
      int idxEmpoLit = 0;
      bool firstLitIsEmpow = false;
      
      bool found_equal_lemma = false;
      vector<int> lemma_sorted = lemma;
      sort(lemma_sorted.begin(), lemma_sorted.end(), [](const int& l1, const int& l2) {return abs(l1) < abs(l2);});
      
      int last_level_DB_status = 0; // the last trail status generated by the propagation of normal DB
      
      for (uint p = 0; !found_equal_lemma && !res && p < possible_empow_lit_idx.size(); ++p) {
        assert(!conflict);
        
        int i = possible_empow_lit_idx[p];
        
        if(lemma.size() == 1) assert(val(lemma[0]) != -1);

        if(val(lemma[i]) != 0) { // should backtrack to a level that its undef
          int lit_level = var(lemma[i]).level;
          assert(lit_level >= 0);
          if(lit_level > 0) backtrack(lit_level-1); // make sure the checked lit is undef now. except units
          assert(lit_level == 0 or val(lemma[i]) == 0);
          if (level < last_level_DB_status) last_level_DB_status = level; // if current level is smaller than last_level_DB_status, than update it
        }
        
        [[maybe_unused]] bool is_emp = is_empowering_wrt_lit_no_bt2_revert(lemma, i);
        
        if (not is_emp) { 
          assert(propagated == trail.size());
          continue;
        }
       
        if(level != last_level_DB_status) { // propagate the original DB
          assert(level >= last_level_DB_status);
          backtrack(last_level_DB_status);
          if(numEmpowerLits > 0) out << "bt " << last_level_DB_status << " "; // only need to print for 2nd empow. lit
        }
        if (level > 0) {++numNotBacktrackTo0; numLevelsReused += level;}
        
        assert(!conflict);
        bool conf_found = false;
        int nDecs = 0;
        for (int k = int(lemma.size()-1); not conf_found and k >= 0; --k) {
          if (k == i) continue;
          if (val(lemma[k]) == 1) conf_found = true; // only for debugging, if true, it is not 1-empowering
          else if (val(lemma[k]) == 0) { // if undef --> set it to false and prop. If false --> skip it
            out << -lemma[k] << " " << flush;
            ++nDecs;
            ++stats.decisions;
            ++stats.decisionsSimRead;
            search_assume_decision(-lemma[k]); // next decision
            if (!propagate()) conf_found = true; // propagation gave a conflict                       
          }
        }
        
        assert(not conf_found and val(lemma[i]) == 0);
        if (lemma.size() > 1) {
          ++nDecs; // the empow.lit
          stats.sumPercDecs += (double)nDecs/lemma.size();
          ++stats.sumNumLemmas;
        }
        
        idxEmpoLit = i;
        ++numEmpowerLits; bool hasMultiAnalysis = false;
        if (i == 0) firstLitIsEmpow = true;
        bool absorbed = false;
        
        while (!res and not absorbed) {
          // Here we should decide the negation of all literals except lemma[i].
          // But this has already been done in the previous call to is_empowering_wrt_lit_no_bt

          ++numAnalysis;
          ++stats.decisions;
          ++stats.decisionsSimRead;
          search_assume_decision(-lemma[i]); // next decision
          out << -lemma[i] << " ";
          
          assert(!conflict);
          propagate();
          assert(conflict);
          
          analyze();
          assert(!unsat);
          assert(!conflict);
          assert(propagated == trail.size()-1);
          int propagated2 = propagated;
          Clause * r = var(trail[propagated]).reason;
          
          propagate();

          if (conflict) { // we proved that in this case the lemma is absorbed wrt lemma[i]
            if (level == 0) {cout << "conflict at dl 0!" << endl << endl << flush; res = 20;} // UNSAT
            else {
              backtrack(level-1);
              last_level_DB_status = level;
              conflict = 0;
              absorbed = true;  // todo: analysis + when no conflict, read next(R)
              if(count) check_and_count(r, lemma_sorted, numSameSize, numSameLemma, numShorterLemma, numSubsumeLemma, found_equal_lemma);
            }
          }
          else {  // no conflict
            bool easy_absortion = (val(lemma[i]) != 0);
            assert(!conflict);
            [[maybe_unused]] uint ts = trail.size();
            propagated = propagated2;  // keep same propagation in two DBs
            propagate2();
            assert(ts == trail.size());
            assert(!conflict);
            last_level_DB_status = level;
            
            if (easy_absortion) {
              absorbed = true;
              if(count) check_and_count(r, lemma_sorted, numSameSize, numSameLemma, numShorterLemma, numSubsumeLemma, found_equal_lemma);
            }
            else {
              int  current_level = level;
              
              bool is_emp = is_empowering_wrt_lit_no_bt2_revert(lemma, i);  // DB2
              ++numEmpowChecksIfNoConf;
              
              if (not is_emp) { //Note: if (conflict or lemma[i] != 0) then level > current_level, 
                                //otherwise (other is true), then level >= current_level
                assert(level >= current_level);
                absorbed = true;
                if(count) check_and_count(r, lemma_sorted, numSameSize, numSameLemma, numShorterLemma, numSubsumeLemma, found_equal_lemma);
              }
              else {
                backtrack(current_level);
                [[maybe_unused]] bool is_emp = is_empowering_wrt_lit_no_bt_revert(lemma, i);
                assert(is_emp);
                assert(var(lemma[i]).level > current_level); // it should be undef, but it's previous level still exist in model.
                
                ++numIsStillEmpowIfNoConf;
                numEmpowerLitsWithMultiAnalysis += (hasMultiAnalysis == false); // increase it only at the first re-analysis
                hasMultiAnalysis = true;
                
                for(int k = int(lemma.size()-1); k >= 0; --k) { // actually just need to print the newly assigned ones > current_level
                  if(k != i) {
                    if (var(lemma[k]).level > current_level) {
                      if(var(lemma[k]).reason == 0) { // only need to write decisions
                        ++stats.decisionsSimRead;
                        out << -lemma[k] << " ";
                      }
                      else ++trueLitNotPrinted;
                    }
                  } // only print the lit at highter level
                }
              }
            }
            
          } // no conflict
        } // end of while()
        
        
      } // end of for() :  finish processing this core lemam
      
      assert(numEmpowerLits > 0);
      if(!res) {out << "R"<< endl; ++stats.restarts;}
      
      sumNumEmpowerLits += numEmpowerLits;
      sumNumEmpowerLitsWithMultiAnalysis += numEmpowerLitsWithMultiAnalysis;
      sumNumAnalysis    += numAnalysis;
      if(numEmpowerLits == 1) {++numOnly1EmpoLit; if(idxEmpoLit == 0) ++numOnly1LitIsFirst;}
      if(firstLitIsEmpow) ++stats.numFirstLitIsEmpow;
      ++numProvableAndEmpower;
     
    
      lemma.clear();
      backtrack(0);  
    }  // go to process next lemma
  
    in.close();
    out.close();
  
    cout << endl << "total #CoreLemmas " << numCoreLemmas << " ,#ProvableAndEmpowerLem " << numProvableAndEmpower << " ,#EmpowerLits " << sumNumEmpowerLits << " ,AVG.#EmpowerLits " << (double)sumNumEmpowerLits/numProvableAndEmpower << " ,#Analysis " << sumNumAnalysis << " ,AVG.Analysis " << (double)sumNumAnalysis/sumNumEmpowerLits << endl;
    
    cout << "sumNumEmpowerLitsWithMultiAnalysis " << sumNumEmpowerLitsWithMultiAnalysis << " ( " << (double)sumNumEmpowerLitsWithMultiAnalysis/sumNumEmpowerLits*100 << "% )" << endl;
    cout << "numEmpowChecksIfNoConf " << numEmpowChecksIfNoConf << " ,numIsStillEmpowIfNoConf " << numIsStillEmpowIfNoConf << " ( " << (double)numIsStillEmpowIfNoConf/numEmpowChecksIfNoConf*100 << "% )" << endl;
    
    cout << "numSameSize     " << numSameSize     << " ,%(numEmpoLits) " << (double)numSameSize/sumNumEmpowerLits*100 << "% ,";
    cout << "numSameLemma    " << numSameLemma    << " ,%(numEmpoLits) " << (double)numSameLemma/sumNumEmpowerLits*100 << "%" << endl;
    cout << "numShorter      " << numShorterLemma << " ,%(numEmpoLits) " << (double)numShorterLemma/sumNumEmpowerLits*100 << "% ,";
    cout << "numSubsumeLem   " << numSubsumeLemma << " ,%(numEmpoLits) " << (double)numSubsumeLemma/sumNumEmpowerLits*100 << "%" << endl;
    cout << "longerLemma     " << (sumNumEmpowerLits-numSameSize-numShorterLemma) << " ,%(numEmpoLits) " << (double)(sumNumEmpowerLits-numSameSize-numShorterLemma)/sumNumEmpowerLits*100 << "%" << endl << endl;
    
    cout << "total sumNumLemmas " << stats.sumNumLemmas << " ,Avg.PercDecs " << stats.sumPercDecs/stats.sumNumLemmas*100 << "%" << endl << endl;
    
    cout << "#firstLitIsEmpow " << stats.numFirstLitIsEmpow << " ( " << (double)stats.numFirstLitIsEmpow/numProvableAndEmpower*100 << "% )" << endl; 
    cout << "total numOnly1EmpoLit " << numOnly1EmpoLit << " ,numOnly1LitIsFirst " << numOnly1LitIsFirst << " ( " << (double)numOnly1LitIsFirst/numOnly1EmpoLit*100 << "% )" << endl; 
    
    
    cout << "total nDecs " << stats.decisions << " ,stats.decisionsSimRead " << stats.decisionsSimRead << " ,nConfs " << stats.conflicts << " ,nRestarts " << stats.restarts << endl; 
  
    cout << "numNotBacktrackTo0:     " << numNotBacktrackTo0 << endl;
    cout << "numLevelsReused:        " << numLevelsReused << endl;
    
    cout << "trueLitNotPrinted: " << trueLitNotPrinted << endl;
    
    cout << "stats.conflicts2: " << stats.conflicts2 << endl << endl << flush;
    
    if (stable) { STOP (stable);   report (']'); }
    else        { STOP (unstable); report ('}'); }

    STOP (search);

    return res;
  }
  
} //namespace CaDiCaL
