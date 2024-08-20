## AMCTS-ATG for Lean4 and Metamath

### 1. Introduction
​	AMCTS-ATG is a method that introduces an adaptive mechanism into MCTS, accompanied by a policy model and a value model, to optimize the search process for generating theorems.

​	Our project is primarily divided into two proof environments: Lean and Metamath, which correspond to the `AMCTS-ATG_Lean4` folder and the `AMCTS-ATG_Metamath` folder, respectively. Below is an introduction to these folders.


#### 1.1  Theorem Generation
* `main_genrate.py`: Place each theorem to be expanded into a separate Lean file, then combine all the files into a single folder. Afterward, iterate through all the files in that folder to start generating the theorems.


#### 1.2  AMCTS
* `mcts.py`: Start generating theorems using the AMCTS method by invoking the `runmcts` method, which executes the steps of selection, expansion, and backpropagation. Perform repeated checks on the generated theorems and generate proof steps. Finally, write the complete theorem into the `example.lean` file in Lean and `output.json` in Metamath.


#### 1.3  Generated Theorems
* `example.lean`: Record all newly generated complete Lean theorems.
* `output.json`: Record all newly generated complete Metamath theorems.


#### 1.4  Interactive Tool
* `Lean4Gym.py`: Our interactive tool for Lean4.
mmverify.py: Our interactive tool for Metamath improved from the traditional mmverify.


#### 1.5  Example
* `CommGroup_basic_example`: Using the `CommGroup_basic_example` folder as an example, it contains some theorems to be expanded, each theorem is placed in a separate file, and the files are named after their respective theorem names.

This example is only applicable to the Lean environment, as the initial state for Metamath is an empty stack and does not require any initial theorems.



### 2. Configuration
If you want to run our program, you need to complete the following steps:

1. Download `AMCTS-ATG.zip`, and unpack it;
2. If you want to run it in the Lean environment, you need to unpack the `AMCTS-ATG_Lean4` folder into your Lean project.
3. Install the required software packages for using AMCTS-ATG:

    ```python
    pip install lake==1.0.1
    pip install numpy==1.26.4
    pip install openai==1.35.13
    pip install pandas==2.2.2
    pip install sympy==1.13.0
    pip install tokenizers==0.19.1
    pip install torch==2.3.0
    pip install tqdm==4.66.4
    pip install transformers==4.42.4
    pip install urllib3==2.2.2
    pip install vllm==0.5.1
    ```

4. If you want to try generating theorems using the examples we provided, enter the following command:

    ```shell
    python main_generate.py
    ```

The generated theorems will be recorded in the `example.lean` file in Lean and `output.json` in Metamath.



### 3. Installation of Importall Library

Importall Library encapsulates all the files that need to be imported for our new theorem files. If you need to install it, you need to modify the `lakefile.lean` file of the Lean project. 

1. Add the following code to lakefile.lean:

    ```lean
    lean_lib «Importall» {

    }
    ```

2. To build Importall, execute the following commands in the root directory of the Lean project:

    ```shell
    lake build Importall
    ```

If you add `import Importall` at the beginning of a LEAN file and the file does not report any errors, it indicates that the installation was successful.



### 4. Installation of Lean4Repl

Lean4Repl is an interactive tool for us in Lean. If you need to install it, you need to modify the `lakefile.lean` file of the Lean project. 

1. Add the following code to lakefile.lean:

    ```lean
    lean_lib «Lean4Repl» {

    }
    ```

2. To build Lean4Repl, execute the following commands in the root directory of the Lean project:

    ```shell
    lake build Lean4Repl
    ```

Note:  If you want to use Lean4Repl, the prefix of the theorem files to be expanded must include `import Lean4Repl`.