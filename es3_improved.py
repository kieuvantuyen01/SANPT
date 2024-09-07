from pysat.formula import CNF
from pysat.solvers import Solver
from itertools import product
import time
from threading import Timer
import os
import ast

# def check_overlap(task1, task2):
def check_overlap(task1, task2):
    # Suppose: task1 = (r1, e1, d1), task2 = (r2, e2, d2)
    # r1_min = r1, r1_max = d1 - e1, d1_min = r1 + e1, d1_max = d1
    # r2_min = r2, r2_max = d2 - e2, d2_min = r2 + e2, d2_max = d2
    # task1 and task2 are overlapped if: 
    # 1. d2_min >= r1_max and r2_max <= d1_min
    # 2. d1_min >= r2_max and r1_max <= d2_min
    # => r2 + e2 >= d1 - e1 and d2 - e2 <= r1 + e1 or r1 + e1 >= d2 - e2 and d1 - e1 <= r2 + e2
    if task2[0] + task2[1] >= task1[2] - task1[1] and task2[2] - task2[1] <= task1[0] + task1[1]:
        return True
    if task1[0] + task1[1] >= task2[2] - task2[1] and task1[2] - task1[1] <= task2[0] + task2[1]:
        return True
    return False

def encode_problem_es3(tasks, resources):
    cnf = CNF()
    max_time = max(task[2] for task in tasks)

    # Variables u[i][j] for task i accessing resource j
    u = [[i * resources + j + 1 for j in range(resources)] for i in range(len(tasks))]

    # Variables z[i][t] for task i accessing some resource at time t
    z = [[len(tasks) * resources + i * max_time + t + 1 for t in range(max_time)] for i in range(len(tasks))]

    # Overlapping: check each pair of tasks to see if they are overlap time, u_i1j -> -u_i2j
    for i in range(len(tasks)):
        for ip in range(i + 1, len(tasks)):
            if check_overlap(tasks[i], tasks[ip]):
                for j in range(resources):
                    cnf.append([-u[i][j], -u[ip][j]])
                    # print(f"Added clause D0: -u{i+1}{j+1} -u{ip+1}{j+1}")

    # Symmetry breaking 1: Assign the tasks to resources if have r_max <= d_min (min of all tasks)
    d_min = min(task[2] for task in tasks)
    fixed_tasks = []
    for i in range(len(tasks)):
        if tasks[i][2] - tasks[i][1] <= d_min:
            fixed_tasks.append(i)
    # Assign each task in fixed_tasks to a resource
    for j, i in enumerate(fixed_tasks):
        if j < resources:
            cnf.append([u[i][j]])
        # print(f"Added clause S1: u{i+1}{j+1}")
    
    # Symmetry breaking 2: 

    # D1: Task i should not access two resources at the same time
    for i in range(len(tasks)):
        for j in range(resources):
            for jp in range(j + 1, resources):
                cnf.append([-u[i][j], -u[i][jp]])
                # print(f"Added clause D1: -u{i+1}{j+1} -u{i+1}{jp+1}")

    # D2: Each task must get some resource
    for i in range(len(tasks)):
        # cnf.append([u[i][j] for j in range(resources)])
        # print(f"Added clause: u{i}0 u{i}1")
        clause = []
        clause_str = []
        for j in range(resources):
            clause.append(u[i][j])
            clause_str.append(f"u{i+1}{j+1}")
        cnf.append(clause)
        # print(f"Added clause D2: {clause_str}")

     # D3: A resource can only be held by one task at a time
    for i in range(len(tasks)):
        for ip in range(i + 1, len(tasks)):
            for j in range(resources):
                for t in range(tasks[i][2]):
                    cnf.append([-z[i][t], -u[i][j], -z[ip][t], -u[ip][j]])
                    # print(f"Added clause D3: -z{i+1}{t} -u{i+1}{j+1} -z{ip+1}{t} -u{ip+1}{j+1}")

    
    # C3: Non-preemptive resource access
    for i in range(len(tasks)):
        z_list = [[[] for _ in range(tasks[i][2] - tasks[i][0])] for _ in range(tasks[i][2] - tasks[i][1] - tasks[i][0] + 1)]

        row = 0
        for t in range(tasks[i][0], tasks[i][2] - tasks[i][1] + 1):
            col = 0
            for tp in range(tasks[i][0], tasks[i][2]):
                if tp < max_time:
                    # print(f"col: {col}, row: {row}")
                    if tp < t:
                        z_list[row][col] = -z[i][tp]
                        # print(f"z_list[row][col]: {z_list[row][col]}")
                    elif tp < t + tasks[i][1]:
                        z_list[row][col] = z[i][tp]
                        # print(f"z_list[row][col]: {z_list[row][col]}")
                    else:
                        z_list[row][col] = -z[i][tp] 
                        # print(f"z_list[row][col]: {z_list[row][col]}")
                    col += 1
            row += 1

        # Ensure that each task need to get access to a resource at least once
        clause = []
        clause_str = []
        for t in range(tasks[i][0], tasks[i][2]):
            clause.append(z[i][t])
            clause_str.append(f"z{i+1}{t}")
        cnf.append(clause)
        # print(f"Added clause C5: {clause_str}")

        # print(z_list)
        
        for combination in product(*z_list):
            clause = list(combination)
            # clause_str = [f"z{i+1}{j+1}" for i, j in enumerate(range(len(combination)))]
            cnf.append(clause)
            # print(f"Added clause C6: {clause}")

    # Link u and z variables
    # Link u and z variables
    for i in range(len(tasks)):
        for t in range(tasks[i][0], tasks[i][2]):
            # If z[i][t] is true, exactly one u[i][j] must be true
            # clause = [-z[i][t]] + [u[i][j] for j in range(resources)]
            clause = [-z[i][t]]
            clause_str = [f"-z{i+1}{t}"]
            for j in range(resources):
                clause.append(u[i][j])
                clause_str.append(f"u{i+1}{j+1}")
            cnf.append(clause)
            # print(f"Added clause C7: {clause_str}")

            for j in range(resources):
                for jp in range(j + 1, resources):
                    clause = [-z[i][t], -u[i][j], -u[i][jp]]
                    clause_str = [f"-z{i+1}{t} -u{i+1}{j+1} -u{i+1}{jp+1}"]
                    cnf.append(clause)
                    # print(f"Added clause C8: {clause_str}")

    # cnf.append([z[0][0]])
    # cnf.append([-z[1][0]])
    # print(f"Added clause C8: z{2}{0}")

    # num_variables = cnf.nv
    # num_clauses = len(cnf.clauses)

    # print(f"Num of variables: {num_variables}")
    # print(f"Num of clauses: {num_clauses}")
    
    return cnf, max_time, u, z

def interrupt(solver):
    solver.interrupt()

def solve_es3(tasks, resources, time_budget=60):
    cnf, max_time, u, z = encode_problem_es3(tasks, resources)


    with Solver(name="glucose4") as solver:
        solver.append_formula(cnf.clauses)
        
        time_budget = 60  # Set your desired time budget in seconds
        timer = Timer(time_budget, interrupt, [solver])
        timer.start()

        start_time = time.time()

        try:
            result = solver.solve_limited(expect_interrupt = True)
        except Exception as e:
            print(f"Solver was interrupted: {e}")
            result = None
        finally:
            timer.cancel()
    
        solve_time = float(format(solver.time(), ".6f"))
        num_variables = solver.nof_vars()
        num_clauses = solver.nof_clauses()
        
        # print(f"Time: {solve_time} s")
        
        # end_time = time.time()
        # solve_time = end_time - start_time
        # print(f"Time: {solve_time:.6f} s")

        res = ""

        if result is True:
            model = solver.get_model()
            if model is None:
                print("Time out")
                res = "Time out"
            else:
                print("SAT")
                res = "SAT"
                for i in range(len(tasks)):
                    for j in range(resources):
                        if model[u[i][j] - 1] > 0:
                            print(f"Task {i} is assigned to resource {j}")
                    for t in range(max_time):
                        # print(f"model[z[i][t] - 1]: {model[z[i][t] - 1]}, z[i][t]: {i+1}{t}")
                        if model[z[i][t] - 1] > 0:
                            print(f"Task {i} is accessing a resource at time {t}")
        else:
            print("UNSAT")
            res = "UNSAT"

        return res, solve_time, num_variables, num_clauses
    
def process_input_files(input_folder, resources=2, time_budget=60):
    results = {}
    for filename in os.listdir(input_folder):
        if filename.startswith("small_") and filename.endswith(".txt"):
            file_path = os.path.join(input_folder, filename)
            with open(file_path, 'r') as f:
                num_tasks = int(f.readline().strip())
                tasks = ast.literal_eval(f.readline().strip())
                print(f"tasks: {tasks}")

            print(f"Processing {filename}...")
            res, solve_time, num_variables, num_clauses = solve_es3(tasks, resources, time_budget)
            results[filename] = {
                "result": res,
                "time": float(solve_time),
                "num_variables": num_variables,
                "num_clauses": num_clauses
            }

    return results

# Main execution
input_folder = "input"
results = process_input_files(input_folder)

# Print summary of results
print("\nSummary of results:")
# Print average time of satisfiable results, average number of variables, average number of clauses
satisfiable_results = [result for result in results.values() if result["result"] == "SAT"]
average_time = sum(result["time"] for result in satisfiable_results) / len(satisfiable_results)
average_variables = sum(result["num_variables"] for result in satisfiable_results) / len(satisfiable_results)
average_clauses = sum(result["num_clauses"] for result in satisfiable_results) / len(satisfiable_results)
print(f"Average time of satisfiable results: {average_time:.6f} s")
print(f"Average number of variables: {average_variables:.6f}")
print(f"Average number of clauses: {average_clauses:.6f}")