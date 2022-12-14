# ontology-matching
match data elements from research site codebooks to ontology terms

To run this code you must clone the repo from github to your local computer. This will produce a folder with the following structure:

`./ontology-matching/`:
* `src/`
* `main.sh`
* `LICENSE`
* `README.md`
* `.gitignore`
  
 For the code to run successfully, you will need input data. There is a test suite abailable on request; please email jack at jackmo375@gmail.com for access. You will also need:
  * python v3+
  * conda for python 3+
  
Once python and conde are installed, use the `ontology-conda-enviroment.yml` file in the `src/` directory to build the python enviroment required to run this code. This program relies on specific versions of certain packages so it is highly reccomended that you create a specific python enviroment for the code using conda and the provided yml file. 

To create the enviroment, simply type:
```
conda env create -f ontology-conda-enviroment.yml
```
Then to activate the enviroment, run:
```
conda activate ontology
```

Finally, before running the code you must create some directories inside `ontology-matching`:
* `input-data/`
* `output-data/`
 
input-data must contain the input files from the test suite as specified above. `output-data` can be empty at this stage. 

Make the main script executable with
```
chmod +x main.sh
```

And, finally, run the program:
```
./main.sh
```

That's it!
  
