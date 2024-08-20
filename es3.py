from pysat.formula import CNF
from pysat.solvers import Solver

def encode_problem_es3(tasks, resources):
    cnf = CNF()

    # Get the maximum time from the tasks' deadlines
    time = max(task[2] for task in tasks)

    # Variables u[i][j] for task i accessing resource j
    u = [[i*resources + j + 1 for j in range(resources)] for i in range(len(tasks))]

    # Variables z[i][t] for task i accessing some resource at time t
    z = [[t + i*time + 1 for t in range(time)] for i in range(len(tasks))]

    # Variables d[i][j][t] for non-preemptive access of resource j by task i starting at time t
    d = [[[t + j*time + i*time*resources + len(tasks)*resources + 1 for t in range(time)] for j in range(resources)] for i in range(len(tasks))]

    # Constraint D1: Task i should not access two resources at the same time
    for i in range(len(tasks)):
        for j in range(resources):
            for jp in range(j+1, resources):
                cnf.append([-u[i][j], -u[i][jp]])

    # Constraint D2: Each task must get some resource
    for i in range(len(tasks)):
        cnf.append([u[i][j] for j in range(resources)])

    # Constraint D3: A resource can only be held by one task at a time
    for i in range(len(tasks)):
        for ip in range(i+1, len(tasks)):
            for j in range(resources):
                for t in range(time):
                    cnf.append([-z[i][t], -u[i][j], -z[ip][t], -u[ip][j]])

    # Constraint D4: Each task must have exactly one start time for accessing a resource non-preemptively
    for i in range(len(tasks)):
        cnf.append([d[i][j][t] for j in range(resources) for t in range(time)])

    # Constraint D5: Linking start variable to z and u variables
    for i in range(len(tasks)):
        for j in range(resources):
            for t in range(time):
                # If d[i][j][t] is true, the task must hold the resource for its entire duration
                for tp in range(t, min(t + tasks[i][1], time)):
                    cnf.append([-d[i][j][t], z[i][tp]])
                    cnf.append([-d[i][j][t], u[i][j]])

                # If d[i][j][t] is true, the task must not hold the resource before t
                for tp in range(0, t):
                    cnf.append([-d[i][j][t], -z[i][tp]])

                # If d[i][j][t] is true, the task must not hold the resource after t + e_i - 1
                for tp in range(t + tasks[i][1], time):
                    cnf.append([-d[i][j][t], -z[i][tp]])

    return cnf, time, u, z, d

# Use the encoding function with a SAT solver
tasks = [(0, 2, 2), (0, 2, 3)]  # Each task is a tuple (ri, ei, di)
resources = 2
cnf, time, u, z, d = encode_problem_es3(tasks, resources)

with Solver(name="glucose4") as solver:
    solver.append_formula(cnf.clauses)
    result = solver.solve()
    if result:
        model = solver.get_model()
        for i in range(len(tasks)):
            for j in range(resources):
                for t in range(time):
                    if model[d[i][j][t]-1] > 0:
                        print(f"Task {i} starts accessing resource {j} at time {t}")
    else:
        print("No solution found")
