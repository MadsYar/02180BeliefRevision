# 02180BeliefRevision

This project implements a belief revision system based on logical entailment and contraction principles. It uses the `sympy` library for symbolic logic manipulation and provides a framework for testing belief revision postulates.

## Features

- **Belief Representation**: Beliefs are represented as logical sentences with priorities.
- **Belief Base**: A collection of beliefs that supports addition, removal, and iteration.
- **Belief Revision**:
  - **Entailment**: Check if a belief base entails a given belief.
  - **Contraction**: Remove beliefs to ensure the base no longer entails a target belief.
  - **Expansion**: Add new beliefs to the base.
- **Postulate Testing**: Includes AGM tests for belief revision such as:
  - Success
  - Inclusion
  - Vacuity
  - Consistency
  - Extensionality

## Requirements

This project requires Python and the `sympy` library. Install the dependencies using:

```bash
pip install -r [requirements.txt](http://_vscodecontentref_/1)¨

## How to Run

To execute the belief revision system and test the postulates, run the `main.py` file:

```bash
python main.py
```

This will execute the predefined test cases and display the results in the terminal.


## File Structure

- `belief_base.py`: Contains the implementation of the `Belief` and `BeliefBase` classes.
- `main.py`: Includes test cases for belief revision postulates and serves as the entry point for the program.
- `requirements.txt`: Lists the required Python dependencies.
