# Computer Verification of Mathematical Proofs: Math496T  (Spring 2026)

This course is based on Mathematics in Lean (MIL) tutorial, which depends on Lean 4, VS Code, and Mathlib.
You can find the original MIL textbook both online and in this repository
in
[html format](https://leanprover-community.github.io/mathematics_in_lean/)
or as a
[pdf document](https://leanprover-community.github.io/mathematics_in_lean/mathematics_in_lean.pdf).

Please make a copy of this math496T repository on your computer.
<!-- Alternatively, you can use Github Codespaces or Gitpod to run Lean and VS Code in the cloud. -->

This version of *Math496T* is designed for [Lean 4](https://leanprover.github.io/) and
[Mathlib](https://github.com/leanprover-community/mathlib4).



## To use this repository on your computer

Do the following:

1. Install Lean 4 and VS Code following
   these [instructions](https://leanprover-community.github.io/get_started.html).

2. Make sure you have [git](https://git-scm.com/) installed.

3. Open a terminal.

   If you have not logged in since you installed Lean and mathlib, then you may need to first type `source ~/.profile` or `source ~/.bash_profile` depending on your OS. If you are on Windows, and don't know how to do this, another option is to restart your computer.

   Go to the directory where you would like this package to live. You do not need to create a new folder yourself, the next command will create a `math496T` subfolder for you.

   Run `git clone https://github.com/cherkis/math496T`.

   Run `cd math496T`

   Run `lake exe cache get` (note: this command currently only works in projects which import mathlib4 as a dependency)

   Launch VS Code, either through your application menu or by typing `code .`. (MacOS users need to take a one-off extra step to be able to launch VS Code from the command line.)

   If you launched VS Code from a menu, on the main screen, or in the File menu, click "Open folder" (just "Open" on a Mac), and choose the folder `math496T` (not one of its subfolders).

   Using the file explorer on the left-hand side, explore and modify everything you want in `My_MIL`. 

   [This step is similar to following these [instructions](https://leanprover-community.github.io/install/project.html#working-on-an-existing-project), but with 
`https://github.com/cherkis/math496T` and `math496T` in place of 
`https://github.com/leanprover-community/mathematics_in_lean.git` and `mathematics_in_lean`
 ]
to fetch the `math496T` repository and open it up in VS Code.

4. Lectures will be posted in `Lectures` folder and homework assignments will appear in `Homework` folder. 
   If you want to move ahead, you can always work on `My_MIL` folder. Each section in the MIL  textbook has an associated Lean file with examples and exercises in `My_MIL` folder, organized by chapter.
   Please do _not_ _modify_ the originals `MIL` folder. It easier to update the repository as it changes (see below).
   Feel free to modify or add your own files to `My_MIL` as you like. We suggest you do all your work only in that folder. 

At any point, you can open MIL textbook in a web browser
at [https://leanprover-community.github.io/mathematics_in_lean/](https://leanprover-community.github.io/mathematics_in_lean/)
and start reading and doing the exercises in VS Code.

This project and this repository will be regularly updated. 
You can update the repository by typing `git pull`
followed by `lake exe cache get` inside the `mathematics_in_lean` folder.
(This assumes that you have not changed the contents of the `MIL`, `Lectures`, or `Homework`  folders,
which is why we suggested only modifying `My_MIL`.)


## To use this repository with Github Codespaces (WARNING: I have not tested this with Math496T.  Let me know if this works for you.)

If you have trouble installing Lean, you can use Lean directly in your browser using Github
Codespaces.
This requires a Github account. If you are signed in to Github, click here:

<a href='https://codespaces.new/cherkis/math496T' target="_blank" rel="noreferrer noopener"><img src='https://github.com/codespaces/badge.svg' alt='Open in GitHub Codespaces' style='max-width: 100%;'></a>

<a href='https://codespaces.new/leanprover-community/mathematics_in_lean' target="_blank" rel="noreferrer noopener"><img src='https://github.com/codespaces/badge.svg' alt='Open in GitHub Codespaces' style='max-width: 100%;'></a>

Make sure the Machine type is `4-core`, and then press `Create codespace`
(this might take a few minutes).
This creates a virtual machine in the cloud,
and installs Lean and Mathlib.

Opening any `.lean` file in the MIL folder will start Lean,
though this may also take a little while.
We suggest copy `MIL` file as `My_MIL` and work `My_MIL` directory, as described
in the instructions above. 
You can update the repository by opening a terminal in the browser
and typing `git pull` followed by `lake exe cache get` as above.

Codespaces offers a certain number of free hours per month. When you are done working,
press `Ctrl/Cmd+Shift+P` on your keyboard, start typing `stop current codespace`, and then
select `Codespaces: Stop Current Codespace` from the list of options.
If you forget, don't worry: the virtual machine will stop itself after a certain
amount of time of inactivity.

To restart a previous workspace, visit <https://github.com/codespaces>.
