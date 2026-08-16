def finish(project):
    """What to say once the loop has stopped, either way."""
    net, report = project.net, project.report
    if net.stopped:
        report.banner(f"solved on attempt {net.iterations}")
        print(project["Student"].get("response"))
    else:
        grader = project["Grader"]
        report.banner("giving up")
        report.note(f"{len(grader.get('errors'))} error(s) and "
                    f"{len(grader.get('sorries'))} sorry(s) remain "
                    f"after {net.iterations} attempts")
