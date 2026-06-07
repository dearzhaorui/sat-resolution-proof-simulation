
`bash
   ./cadical-master --chrono=0 cnf/add4.cnf 4.prf   # print binary proof

   ./drat-trim cnf/add4.cnf 4.prf -l 4.core-lemmas  # write core lemmas

   ./build/cadical --chrono=0 -core 4.core-lemmas -simout 4.txt --ws cnf/add4.cnf prf.txt  # write branching sequence
`
