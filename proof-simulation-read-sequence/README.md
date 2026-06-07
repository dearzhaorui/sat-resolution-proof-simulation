
`bash

   ./build/cadical --chrono=0 -simout 4.txt --rs cnf/add4.cnf prf.txt  # read branching sequence
   
   ./drat-trim cnf/add4.cnf prf.txt    # verify
`
