import os
import re
#for each folder in runs folder
loc=os.getcwd();#get current working directory location #assumption is that this script is placed in the 'runs' folder
programs = os.listdir(loc);#get all entries/elements in the directory
for program in programs:
#{
	#get program(e.g.batch100) folder path
	batch_folder_path=os.path.join(loc,program);
	if (os.path.isdir(batch_folder_path)):#if directory-correct only the filenames of all files inside
	#{
		#for each smt file in this folder
		files=os.listdir(batch_folder_path);
		for file in files:
		#{
			if ('.smt2' in file): #correct names of all smt files
			#{
				org_altered_file_path=os.path.join(batch_folder_path,file);
				correctedfile=file.replace('.smt2_from','_from');
				correctedfile=correctedfile.replace('.smt2_altered','_altered');
				correctedfile='nw_'+ correctedfile;
				correctedfile_path=os.path.join(batch_folder_path,correctedfile);
				with open(org_altered_file_path) as ifile:
					with open(correctedfile_path, 'w') as ofile:
						for line in ifile:
							ofile.write(line);
				#remove original altered file
				if os.path.exists(org_altered_file_path):
				#{
					os.remove(org_altered_file_path);
				#}
			#}
		#}
	#}
#}